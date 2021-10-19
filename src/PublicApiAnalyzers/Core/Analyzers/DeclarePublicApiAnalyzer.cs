﻿// Copyright (c) Microsoft.  All Rights Reserved.  Licensed under the MIT license.  See License.txt in the project root for license information.

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;

using DiagnosticIds = Roslyn.Diagnostics.Analyzers.RoslynDiagnosticIds;

namespace Microsoft.CodeAnalysis.PublicApiAnalyzers
{
    using static PublicApiAnalyzerResources;

    [DiagnosticAnalyzer(LanguageNames.CSharp, LanguageNames.VisualBasic)]
    public sealed partial class DeclarePublicApiAnalyzer : DiagnosticAnalyzer
    {
        internal const string ShippedFileNamePrefix = "PublicAPI.Shipped";
        internal const string ShippedFileName = "PublicAPI.Shipped.txt";
        internal const string UnshippedFileNamePrefix = "PublicAPI.Unshipped";
        internal const string Extension = ".txt";
        internal const string UnshippedFileName = "PublicAPI.Unshipped.txt";
        internal const string PublicApiNamePropertyBagKey = "PublicAPIName";
        internal const string PublicApiNameWithNullabilityPropertyBagKey = "PublicAPINameWithNullability";
        internal const string MinimalNamePropertyBagKey = "MinimalName";
        internal const string PublicApiNamesOfSiblingsToRemovePropertyBagKey = "PublicApiNamesOfSiblingsToRemove";
        internal const string PublicApiNamesOfSiblingsToRemovePropertyBagValueSeparator = ";;";
        internal const string RemovedApiPrefix = "*REMOVED*";
        internal const string NullableEnable = "#nullable enable";
        internal const string InvalidReasonShippedCantHaveRemoved = "The shipped API file can't have removed members";
        internal const string InvalidReasonMisplacedNullableEnable = "The '#nullable enable' marker can only appear as the first line in the shipped API file";
        internal const string PublicApiIsShippedPropertyBagKey = "PublicAPIIsShipped";
        internal const string FileName = "FileName";

        private const char ObliviousMarker = '~';

        /// <summary>
        /// Boolean option to configure if public API analyzer should bail out silently if public API files are missing.
        /// </summary>
        private const string BailOnMissingPublicApiFilesEditorConfigOptionName = "dotnet_public_api_analyzer.require_api_files";

        internal static readonly DiagnosticDescriptor DeclareNewApiRule = new(
            id: DiagnosticIds.DeclarePublicApiRuleId,
            title: CreateLocalizableResourceString(nameof(DeclarePublicApiTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(DeclarePublicApiMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            description: CreateLocalizableResourceString(nameof(DeclarePublicApiDescription)),
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.Telemetry);

        internal static readonly DiagnosticDescriptor AnnotateApiRule = new(
            id: DiagnosticIds.AnnotatePublicApiRuleId,
            title: CreateLocalizableResourceString(nameof(AnnotatePublicApiTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(AnnotatePublicApiMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            description: CreateLocalizableResourceString(nameof(AnnotatePublicApiDescription)),
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.Telemetry);

        internal static readonly DiagnosticDescriptor ObliviousApiRule = new(
            id: DiagnosticIds.ObliviousPublicApiRuleId,
            title: CreateLocalizableResourceString(nameof(ObliviousPublicApiTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(ObliviousPublicApiMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            description: CreateLocalizableResourceString(nameof(ObliviousPublicApiDescription)),
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.Telemetry);

        internal static readonly DiagnosticDescriptor RemoveDeletedApiRule = new(
            id: DiagnosticIds.RemoveDeletedApiRuleId,
            title: CreateLocalizableResourceString(nameof(RemoveDeletedApiTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(RemoveDeletedApiMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            description: CreateLocalizableResourceString(nameof(RemoveDeletedApiDescription)),
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.CompilationEndAndTelemetry);

        internal static readonly DiagnosticDescriptor RemovedApiIsNotActuallyRemovedRule = new(
           id: DiagnosticIds.RemovedApiIsNotActuallyRemovedRuleId,
           title: CreateLocalizableResourceString(nameof(RemovedApiIsNotActuallyRemovedTitle)),
           messageFormat: CreateLocalizableResourceString(nameof(RemovedApiIsNotActuallyRemovedMessage)),
           category: "ApiDesign",
           defaultSeverity: DiagnosticSeverity.Warning,
           isEnabledByDefault: true,
           helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
           customTags: WellKnownDiagnosticTagsExtensions.CompilationEndAndTelemetry);

        internal static readonly DiagnosticDescriptor ExposedNoninstantiableType = new(
            id: DiagnosticIds.ExposedNoninstantiableTypeRuleId,
            title: CreateLocalizableResourceString(nameof(ExposedNoninstantiableTypeTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(ExposedNoninstantiableTypeMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.Telemetry);

        internal static readonly DiagnosticDescriptor PublicApiFilesInvalid = new(
            id: DiagnosticIds.PublicApiFilesInvalid,
            title: CreateLocalizableResourceString(nameof(PublicApiFilesInvalidTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(PublicApiFilesInvalidMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.CompilationEndAndTelemetry);

        internal static readonly DiagnosticDescriptor PublicApiFileMissing = new(
            id: DiagnosticIds.PublicApiFileMissing,
            title: CreateLocalizableResourceString(nameof(PublicApiFileMissingTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(PublicApiFileMissingMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.CompilationEndAndTelemetry);

        internal static readonly DiagnosticDescriptor DuplicateSymbolInApiFiles = new(
            id: DiagnosticIds.DuplicatedSymbolInPublicApiFiles,
            title: CreateLocalizableResourceString(nameof(DuplicateSymbolsInPublicApiFilesTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(DuplicateSymbolsInPublicApiFilesMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.CompilationEndAndTelemetry);

        internal static readonly DiagnosticDescriptor AvoidMultipleOverloadsWithOptionalParameters = new(
            id: DiagnosticIds.AvoidMultipleOverloadsWithOptionalParameters,
            title: CreateLocalizableResourceString(nameof(AvoidMultipleOverloadsWithOptionalParametersTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(AvoidMultipleOverloadsWithOptionalParametersMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            helpLinkUri: @"https://github.com/dotnet/roslyn/blob/main/docs/Adding%20Optional%20Parameters%20in%20Public%20API.md",
            customTags: WellKnownDiagnosticTagsExtensions.Telemetry);

        internal static readonly DiagnosticDescriptor OverloadWithOptionalParametersShouldHaveMostParameters = new(
            id: DiagnosticIds.OverloadWithOptionalParametersShouldHaveMostParameters,
            title: CreateLocalizableResourceString(nameof(OverloadWithOptionalParametersShouldHaveMostParametersTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(OverloadWithOptionalParametersShouldHaveMostParametersMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            helpLinkUri: @"https://github.com/dotnet/roslyn/blob/main/docs/Adding%20Optional%20Parameters%20in%20Public%20API.md",
            customTags: WellKnownDiagnosticTagsExtensions.Telemetry);

        internal static readonly DiagnosticDescriptor ShouldAnnotateApiFilesRule = new(
            id: DiagnosticIds.ShouldAnnotateApiFilesRuleId,
            title: CreateLocalizableResourceString(nameof(ShouldAnnotateApiFilesTitle)),
            messageFormat: CreateLocalizableResourceString(nameof(ShouldAnnotateApiFilesMessage)),
            category: "ApiDesign",
            defaultSeverity: DiagnosticSeverity.Warning,
            isEnabledByDefault: true,
            description: CreateLocalizableResourceString(nameof(ShouldAnnotateApiFilesDescription)),
            helpLinkUri: "https://github.com/dotnet/roslyn-analyzers/blob/main/src/PublicApiAnalyzers/PublicApiAnalyzers.Help.md",
            customTags: WellKnownDiagnosticTagsExtensions.Telemetry);

        internal static readonly SymbolDisplayFormat ShortSymbolNameFormat =
            new(
                globalNamespaceStyle: SymbolDisplayGlobalNamespaceStyle.OmittedAsContaining,
                typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameOnly,
                propertyStyle: SymbolDisplayPropertyStyle.NameOnly,
                genericsOptions: SymbolDisplayGenericsOptions.IncludeTypeParameters,
                memberOptions:
                    SymbolDisplayMemberOptions.None,
                parameterOptions:
                    SymbolDisplayParameterOptions.None,
                miscellaneousOptions:
                    SymbolDisplayMiscellaneousOptions.None);

        private const int IncludeNullableReferenceTypeModifier = 1 << 6;
        private const int IncludeNonNullableReferenceTypeModifier = 1 << 8;

        private static readonly SymbolDisplayFormat s_publicApiFormat =
            new(
                globalNamespaceStyle: SymbolDisplayGlobalNamespaceStyle.OmittedAsContaining,
                typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces,
                propertyStyle: SymbolDisplayPropertyStyle.ShowReadWriteDescriptor,
                genericsOptions: SymbolDisplayGenericsOptions.IncludeTypeParameters,
                memberOptions:
                    SymbolDisplayMemberOptions.IncludeParameters |
                    SymbolDisplayMemberOptions.IncludeContainingType |
                    SymbolDisplayMemberOptions.IncludeExplicitInterface |
                    SymbolDisplayMemberOptions.IncludeModifiers |
                    SymbolDisplayMemberOptions.IncludeConstantValue,
                parameterOptions:
                    SymbolDisplayParameterOptions.IncludeExtensionThis |
                    SymbolDisplayParameterOptions.IncludeParamsRefOut |
                    SymbolDisplayParameterOptions.IncludeType |
                    SymbolDisplayParameterOptions.IncludeName |
                    SymbolDisplayParameterOptions.IncludeDefaultValue,
                miscellaneousOptions:
                    SymbolDisplayMiscellaneousOptions.UseSpecialTypes);

        private static readonly SymbolDisplayFormat s_publicApiFormatWithNullability =
            s_publicApiFormat.WithMiscellaneousOptions(
                SymbolDisplayMiscellaneousOptions.UseSpecialTypes |
                (SymbolDisplayMiscellaneousOptions)IncludeNullableReferenceTypeModifier |
                (SymbolDisplayMiscellaneousOptions)IncludeNonNullableReferenceTypeModifier);

        public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics { get; } =
            ImmutableArray.Create(DeclareNewApiRule, AnnotateApiRule, ObliviousApiRule, RemoveDeletedApiRule, ExposedNoninstantiableType,
                PublicApiFilesInvalid, PublicApiFileMissing, DuplicateSymbolInApiFiles, AvoidMultipleOverloadsWithOptionalParameters,
                OverloadWithOptionalParametersShouldHaveMostParameters, ShouldAnnotateApiFilesRule, RemovedApiIsNotActuallyRemovedRule);

        public override void Initialize(AnalysisContext context)
        {
            context.EnableConcurrentExecution();

            // Analyzer needs to get callbacks for generated code, and might report diagnostics in generated code.
            context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.Analyze | GeneratedCodeAnalysisFlags.ReportDiagnostics);

            context.RegisterCompilationStartAction(OnCompilationStart);
        }

        private void OnCompilationStart(CompilationStartAnalysisContext compilationContext)
        {
            var errors = new List<Diagnostic>();

            // Switch to "RegisterAdditionalFileAction" available in Microsoft.CodeAnalysis "3.8.x" to report additional file diagnostics: https://github.com/dotnet/roslyn-analyzers/issues/3918
            if (!TryGetApiData(compilationContext.Options, compilationContext.Compilation, errors, compilationContext.CancellationToken, out ApiData shippedData, out ApiData unshippedData) ||
                !ValidateApiFiles(shippedData, unshippedData, errors))
            {
                compilationContext.RegisterCompilationEndAction(context =>
                {
                    foreach (Diagnostic cur in errors)
                    {
                        context.ReportDiagnostic(cur);
                    }
                });

                return;
            }

            Debug.Assert(errors.Count == 0);

            var impl = new Impl(compilationContext.Compilation, shippedData, unshippedData);
            compilationContext.RegisterSymbolAction(
                impl.OnSymbolAction,
                SymbolKind.NamedType,
                SymbolKind.Event,
                SymbolKind.Field,
                SymbolKind.Method);
            compilationContext.RegisterSymbolAction(
                impl.OnPropertyAction,
                SymbolKind.Property);
            compilationContext.RegisterCompilationEndAction(impl.OnCompilationEnd);
        }

        private static ApiData ReadApiData(List<(string path, SourceText sourceText)> data, bool isShippedApi)
        {
            var apiBuilder = ImmutableArray.CreateBuilder<ApiLine>();
            var removedBuilder = ImmutableArray.CreateBuilder<RemovedApiLine>();
            var maxNullableRank = -1;

            foreach (var (path, sourceText) in data)
            {
                int rank = -1;

                foreach (TextLine line in sourceText.Lines)
                {
                    string text = line.ToString();
                    if (string.IsNullOrWhiteSpace(text))
                    {
                        continue;
                    }

                    rank++;

                    if (text == NullableEnable)
                    {
                        maxNullableRank = Math.Max(rank, maxNullableRank);
                        continue;
                    }

                    var apiLine = new ApiLine(text, line.Span, sourceText, path, isShippedApi);
                    if (text.StartsWith(RemovedApiPrefix, StringComparison.Ordinal))
                    {
                        string removedtext = text[RemovedApiPrefix.Length..];
                        removedBuilder.Add(new RemovedApiLine(removedtext, apiLine));
                    }
                    else
                    {
                        apiBuilder.Add(apiLine);
                    }
                }
            }

            return new ApiData(apiBuilder.ToImmutable(), removedBuilder.ToImmutable(), maxNullableRank);
        }

        private static bool TryGetApiData(AnalyzerOptions analyzerOptions, Compilation compilation, List<Diagnostic> errors, CancellationToken cancellationToken, out ApiData shippedData, out ApiData unshippedData)
        {
            if (!TryGetApiText(analyzerOptions.AdditionalFiles, cancellationToken, out var shippedText, out var unshippedText))
            {
                if (shippedText == null && unshippedText == null)
                {
                    if (TryGetEditorConfigOptionForMissingFiles(analyzerOptions, compilation, out var silentlyBailOutOnMissingApiFiles) &&
                        silentlyBailOutOnMissingApiFiles)
                    {
                        shippedData = default;
                        unshippedData = default;
                        return false;
                    }

                    // Bootstrapping public API files.
                    (shippedData, unshippedData) = (ApiData.Empty, ApiData.Empty);
                    return true;
                }

                var missingFileName = shippedText == null ? ShippedFileName : UnshippedFileName;
                errors.Add(Diagnostic.Create(PublicApiFileMissing, Location.None, missingFileName));
                shippedData = default;
                unshippedData = default;
                return false;
            }

            shippedData = ReadApiData(shippedText, isShippedApi: true);
            unshippedData = ReadApiData(unshippedText, isShippedApi: false);
            return true;
        }

        private static bool TryGetEditorConfigOptionForMissingFiles(AnalyzerOptions analyzerOptions, Compilation compilation, out bool optionValue)
        {
            optionValue = false;
            try
            {
                var provider = analyzerOptions.GetType().GetRuntimeProperty("AnalyzerConfigOptionsProvider")?.GetValue(analyzerOptions);
                if (provider == null || !compilation.SyntaxTrees.Any())
                {
                    return false;
                }

                var getOptionsMethod = provider.GetType().GetRuntimeMethods().FirstOrDefault(m => m.Name == "GetOptions");
                if (getOptionsMethod == null)
                {
                    return false;
                }

                var options = getOptionsMethod.Invoke(provider, new object[] { compilation.SyntaxTrees.First() });
                var tryGetValueMethod = options.GetType().GetRuntimeMethods().FirstOrDefault(m => m.Name == "TryGetValue");
                if (tryGetValueMethod == null)
                {
                    return false;
                }

                // bool TryGetValue(string key, out string value);
                var parameters = new object?[] { BailOnMissingPublicApiFilesEditorConfigOptionName, null };
                if (tryGetValueMethod.Invoke(options, parameters) is not bool hasOption ||
                    !hasOption)
                {
                    return false;
                }

                if (parameters[1] is not string value ||
                    !bool.TryParse(value, out var boolValue))
                {
                    return false;
                }

                optionValue = boolValue;
                return true;
            }
#pragma warning disable CA1031 // Do not catch general exception types
            catch
#pragma warning restore CA1031 // Do not catch general exception types
            {
                // Gracefully handle any exception from reflection.
                return false;
            }
        }

        private static bool IsFile(string path, string prefix, StringComparison comparison)
            => path.StartsWith(prefix, comparison) && path.EndsWith(Extension, comparison);

        private static bool TryGetApiText(
            ImmutableArray<AdditionalText> additionalTexts,
            CancellationToken cancellationToken,
            [NotNullWhen(returnValue: true)] out List<(string path, SourceText text)>? shippedText,
            [NotNullWhen(returnValue: true)] out List<(string path, SourceText text)>? unshippedText)
        {
            shippedText = null;
            unshippedText = null;

            StringComparison comparison = StringComparison.Ordinal;
            foreach (AdditionalText additionalText in additionalTexts)
            {
                cancellationToken.ThrowIfCancellationRequested();

                string fileName = Path.GetFileName(additionalText.Path);

                bool isShippedFile = IsFile(fileName, ShippedFileNamePrefix, comparison);
                bool isUnshippedFile = IsFile(fileName, UnshippedFileNamePrefix, comparison);

                if (isShippedFile || isUnshippedFile)
                {
                    SourceText text = additionalText.GetText(cancellationToken);

                    if (text == null)
                    {
                        continue;
                    }

                    var data = (additionalText.Path, text);
                    if (isShippedFile)
                    {
                        if (shippedText is null)
                        {
                            shippedText = new();
                        }

                        shippedText.Add(data);
                    }

                    if (isUnshippedFile)
                    {
                        if (unshippedText is null)
                        {
                            unshippedText = new();
                        }

                        unshippedText.Add(data);
                    }
                    continue;
                }
            }

            return shippedText != null && unshippedText != null;
        }

        private static bool ValidateApiFiles(ApiData shippedData, ApiData unshippedData, List<Diagnostic> errors)
        {
            if (!shippedData.RemovedApiList.IsEmpty)
            {
                errors.Add(Diagnostic.Create(PublicApiFilesInvalid, Location.None, InvalidReasonShippedCantHaveRemoved));
            }

            if (shippedData.NullableRank > 0)
            {
                // '#nullable enable' must be on the first line
                errors.Add(Diagnostic.Create(PublicApiFilesInvalid, Location.None, InvalidReasonMisplacedNullableEnable));
            }

            if (unshippedData.NullableRank > 0)
            {
                // '#nullable enable' must be on the first line
                errors.Add(Diagnostic.Create(PublicApiFilesInvalid, Location.None, InvalidReasonMisplacedNullableEnable));
            }

            var publicApiMap = new Dictionary<string, ApiLine>(StringComparer.Ordinal);
            ValidateApiList(publicApiMap, shippedData.ApiList, errors);
            ValidateApiList(publicApiMap, unshippedData.ApiList, errors);

            return errors.Count == 0;
        }

        private static void ValidateApiList(Dictionary<string, ApiLine> publicApiMap, ImmutableArray<ApiLine> apiList, List<Diagnostic> errors)
        {
            foreach (ApiLine cur in apiList)
            {
                string textWithoutOblivious = cur.Text.TrimStart(ObliviousMarker);
                if (publicApiMap.TryGetValue(textWithoutOblivious, out ApiLine existingLine))
                {
                    LinePositionSpan existingLinePositionSpan = existingLine.SourceText.Lines.GetLinePositionSpan(existingLine.Span);
                    Location existingLocation = Location.Create(existingLine.Path, existingLine.Span, existingLinePositionSpan);

                    LinePositionSpan duplicateLinePositionSpan = cur.SourceText.Lines.GetLinePositionSpan(cur.Span);
                    Location duplicateLocation = Location.Create(cur.Path, cur.Span, duplicateLinePositionSpan);
                    errors.Add(Diagnostic.Create(DuplicateSymbolInApiFiles, duplicateLocation, new[] { existingLocation }, cur.Text));
                }
                else
                {
                    publicApiMap.Add(textWithoutOblivious, cur);
                }
            }
        }
    }
}
