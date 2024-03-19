// Copyright (c) Microsoft.  All Rights Reserved.  Licensed under the MIT license.  See License.txt in the project root for license information.

using System.Collections.Generic;
using System.Collections;
using System;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using System.Threading;
using Analyzer.Utilities;
using Analyzer.Utilities.Extensions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Operations;

namespace Microsoft.NetCore.Analyzers.Performance
{
    using static MicrosoftNetCoreAnalyzersResources;

    /// <summary>
    /// CA1870: <inheritdoc cref="UseSearchValuesTitle"/>
    /// </summary>
    public abstract class UseIndexOfAnyInsteadOfLoop : DiagnosticAnalyzer
    {
        internal const string DiagnosticId = "CA1871";

        internal static readonly DiagnosticDescriptor Rule = DiagnosticDescriptorHelper.Create(
            DiagnosticId,
            CreateLocalizableResourceString(nameof(UseSearchValuesTitle)),
            CreateLocalizableResourceString(nameof(UseSearchValuesMessage)),
            DiagnosticCategory.Performance,
            RuleLevel.IdeSuggestion,
            description: CreateLocalizableResourceString(nameof(UseSearchValuesDescription)),
            isPortedFxCopRule: false,
            isDataflowRule: false);

        public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics { get; } = ImmutableArray.Create(Rule);

        public override void Initialize(AnalysisContext context)
        {
            context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
            context.EnableConcurrentExecution();

            context.RegisterCompilationStartAction(context =>
            {
                if (!context.Compilation.TryGetOrCreateTypeByMetadataName(WellKnownTypeNames.SystemBuffersSearchValues, out _) ||
                    !context.Compilation.TryGetOrCreateTypeByMetadataName(WellKnownTypeNames.SystemReadOnlySpan1, out _))
                {
                    return;
                }

                context.RegisterOperationAction(context =>
                {
#pragma warning disable CA1031 // Do not catch general exception types
                    try
                    {
                        AnalyzeLoopOperation(context);
                    }
                    catch (Exception ex)
                    {
                        Console.WriteLine(ex);
                    }
#pragma warning restore CA1031 // Do not catch general exception types
                }, OperationKind.Loop);
            });
        }

        private static void AnalyzeLoopOperation(OperationAnalysisContext context)
        {
            var loop = (ILoopOperation)context.Operation;

            ILocalSymbol? iSymbol = null;
            ISymbol? textSymbol = null;
            ILocalSymbol? charLocal = null;

            if (loop is IForLoopOperation forLoop)
            {
                if (!IsSimpleForLoopToStringLength(forLoop, out iSymbol, out textSymbol))
                {
                    return;
                }
            }
            else if (loop is IForEachLoopOperation foreachLoop)
            {
                if (!IsForeachCharInStringLoop(foreachLoop, out charLocal, out textSymbol))
                {
                    return;
                }
            }
            else if (loop is IWhileLoopOperation whileLoop)
            {
                if (!IsWhileLoopOverStringLength(whileLoop, out iSymbol, out textSymbol))
                {
                    return;
                }
            }

            if (loop.Body is not IBlockOperation body)
            {
                return;
            }

            ImmutableArray<IOperation> operations = body.Operations;

            if (operations.Length == 0)
            {
                return;
            }

            // For now let's look only at a single if/return
            // for (int i = 0; i < name.Length; i++)
            // {
            //     char c = name[i];
            //     if (!(char.IsAsciiLetterOrDigit(c) || c == '.' || c == '-' || c == '_'))
            //         return false;
            // }

            int indexToInspect = 0;

            if (charLocal is null && operations.Length > 1 && textSymbol is not null && iSymbol is not null)
            {
                // char c = name[i];
                if (IsSingleVariableDeclaration(operations[0], out charLocal, out IVariableInitializerOperation? charInitializer) &&
                    charInitializer.Value.Type?.SpecialType == SpecialType.System_Char &&
                    IsSpanOrStringIndexerWithIGetterOperation(charInitializer.Value, textSymbol, iSymbol))
                {
                    indexToInspect = 1;
                }
                else
                {
                    charLocal = null;
                }
            }

            // if (condition)
            //     return ...;
            if (operations[indexToInspect] is not IConditionalOperation ifStatement ||
                ifStatement.WhenFalse is not null ||
                ifStatement.WhenTrue is not IBlockOperation trueBlock ||
                trueBlock.Operations.Length != 1 ||
                trueBlock.Operations[0] is not (IReturnOperation or IThrowOperation or IBranchOperation))
            {
                return;
            }

            if (!CharacterCheckAnalyzer.TryGetRanges(context.Operation.SemanticModel!, ifStatement.Condition, charLocal, textSymbol, iSymbol, out _, context.CancellationToken))
            {
                return;
            }

            context.ReportDiagnostic(loop.CreateDiagnostic(Rule));
        }

        private static bool IsSimpleForLoopToStringLength(IForLoopOperation loop, [NotNullWhen(true)] out ILocalSymbol? iSymbol, [NotNullWhen(true)] out ISymbol? textSymbol)
        {
            iSymbol = null;
            textSymbol = null;

            if (loop.Locals.Length != 1 ||
                loop.Before.Length != 1 ||
                loop.AtLoopBottom.Length != 1)
            {
                return false;
            }

            iSymbol = loop.Locals[0];

            // for (int i = 0; *; *)
            if (iSymbol.Type.SpecialType is not SpecialType.System_Int32 ||
                !IsSingleVariableDeclaration(loop.Before[0], out ILocalSymbol? declaredSymbol, out _) ||
                declaredSymbol.Name != iSymbol.Name
                //||
                //!HasConstantValue(iInitializer.Value, out int initialValue) ||
                //initialValue != 0
                )
            {
                return false;
            }

            // for (int i = 0; i < text.Length; *)
            if (loop.Condition is not IBinaryOperation binaryOperation ||
                binaryOperation.OperatorKind != BinaryOperatorKind.LessThan ||
                binaryOperation.LeftOperand is not ILocalReferenceOperation leftLocalReference ||
                leftLocalReference.Local.Name != iSymbol.Name ||
                binaryOperation.RightOperand is not IMemberReferenceOperation rightMemberReference ||
                rightMemberReference.Member.Name != "Length" ||
                rightMemberReference.Instance is not { } rightMemberInstance ||
                !IsStringOrSpanOfChar(rightMemberInstance.Type) ||
                !IsLocalOrParameterReference(rightMemberInstance, out textSymbol))
            {
                return false;
            }

            // for (int i = 0; i < text.Length; i++)
            if (loop.AtLoopBottom[0] is not IExpressionStatementOperation expressionStatement ||
                expressionStatement.Operation is not IIncrementOrDecrementOperation incrementOperation ||
                incrementOperation.Target is not ILocalReferenceOperation incrementTargetReference ||
                incrementTargetReference.Local.Name != iSymbol.Name ||
                incrementOperation.Kind != OperationKind.Increment)
            {
                return false;
            }

            return true;
        }

        private static bool IsForeachCharInStringLoop(IForEachLoopOperation loop, [NotNullWhen(true)] out ILocalSymbol? charLocal, [NotNullWhen(true)] out ISymbol? textSymbol)
        {
            IOperation collection = loop.Collection;

            if (collection is IConversionOperation conversion && conversion.IsImplicit)
            {
                collection = conversion.Operand;
            }

            if (IsLocalOrParameterReference(collection, out textSymbol) &&
                loop.Locals is [var local] &&
                local.Type.SpecialType == SpecialType.System_Char)
            {
                charLocal = local;
                return true;
            }

            charLocal = null;
            textSymbol = null;
            return false;
        }

        private static bool IsWhileLoopOverStringLength(IWhileLoopOperation loop, [NotNullWhen(true)] out ILocalSymbol? iSymbol, [NotNullWhen(true)] out ISymbol? textSymbol)
        {
            iSymbol = null;
            textSymbol = null;

            if (loop.Condition is not IBinaryOperation binaryOperation ||
                binaryOperation.OperatorKind != BinaryOperatorKind.LessThan ||
                binaryOperation.LeftOperand is not ILocalReferenceOperation leftLocalReference ||
                binaryOperation.RightOperand is not IMemberReferenceOperation rightMemberReference ||
                rightMemberReference.Member.Name != "Length" ||
                rightMemberReference.Instance is not { } rightMemberInstance ||
                !IsStringOrSpanOfChar(rightMemberInstance.Type) ||
                !IsLocalOrParameterReference(rightMemberInstance, out textSymbol))
            {
                return false;
            }

            iSymbol = leftLocalReference.Local;

            if (loop.Body is not IBlockOperation body ||
                body.Operations.Length == 0 ||
                body.Operations[^1] is not IExpressionStatementOperation expressionStatement ||
                expressionStatement.Operation is not IIncrementOrDecrementOperation incrementOperation ||
                incrementOperation.Target is not ILocalReferenceOperation incrementTargetReference ||
                incrementTargetReference.Local.Name != iSymbol.Name ||
                incrementOperation.Kind != OperationKind.Increment)
            {
                return false;
            }

            return true;
        }

        public static bool IsSpanOrStringIndexerWithIGetterOperation(IOperation operation, ISymbol textSymbol, ILocalSymbol iSymbol)
        {
            if (operation is IPropertyReferenceOperation textIndexerReference &&
                IsLocalOrParameterReference(textIndexerReference.Instance, out ISymbol? symbol) &&
                symbol.Name == textSymbol.Name &&
                textIndexerReference.Arguments is [var argument] &&
                IsLocalOrParameterReference(argument.Value, out ISymbol? indexArgument) &&
                indexArgument.Name == iSymbol.Name)
            {
                string expectedName = textIndexerReference.Instance?.Type?.SpecialType == SpecialType.System_String
                    ? "get_Chars"
                    : "get_Item";

                return textIndexerReference.Property.GetMethod?.Name == expectedName;
            }

            return false;
        }

        private static bool IsLocalOrParameterReference(IOperation? operation, [NotNullWhen(true)] out ISymbol? symbol)
        {
            if (operation is ILocalReferenceOperation localReference)
            {
                symbol = localReference.Local;
                return true;
            }

            if (operation is IParameterReferenceOperation parameterReference)
            {
                symbol = parameterReference.Parameter;
                return true;
            }

            symbol = null;
            return false;
        }

        private static bool IsSingleVariableDeclaration(IOperation operation, [NotNullWhen(true)] out ILocalSymbol? symbol, [NotNullWhen(true)] out IVariableInitializerOperation? initializer)
        {
            if (operation is IVariableDeclarationGroupOperation declarationGroup &&
                declarationGroup.Declarations is [var declaration] &&
                declaration.Declarators is [var declarator] &&
                declarator.Initializer is { } variableInitializer)
            {
                symbol = declarator.Symbol;
                initializer = variableInitializer;
                return true;
            }

            symbol = null;
            initializer = null;
            return false;
        }

        private static bool IsStringOrSpanOfChar(ITypeSymbol? type)
        {
            if (type?.SpecialType == SpecialType.System_String)
            {
                return true;
            }

            if (type is INamedTypeSymbol namedType)
            {
                if (namedType.Arity == 1 &&
                    namedType.TypeArguments[0].SpecialType == SpecialType.System_Char &&
                    namedType.ConstructedFrom?.Name is "Span" or "ReadOnlySpan" &&
                    namedType.ConstructedFrom.ContainingNamespace.Name == "System")
                {
                    return true;
                }
            }

            return false;
        }

        internal static class CharacterCheckAnalyzer
        {
            public static bool TryGetRanges(
                SemanticModel semanticModel,
                IOperation condition,
                ILocalSymbol? charLocal,
                ISymbol? textSymbol,
                ILocalSymbol? iSymbol,
                [NotNullWhen(true)] out List<(char Start, char End)>? ranges,
                CancellationToken cancellationToken)
            {
                try
                {
                    var context = new Context(semanticModel, charLocal, textSymbol, iSymbol, parameterSymbol: null, cancellationToken);

                    if (TryGetChars(ref context, condition, out Chars chars))
                    {
                        // TODO Ranges
                        ranges = default!;
                        return true;
                    }
                }
                catch (InsufficientExecutionStackException) { }

                ranges = default;
                return false;
            }

            private readonly struct Context : IEquatable<Context>
            {
                public SemanticModel SemanticModel { get; }
                public CancellationToken CancellationToken { get; }

                private readonly ILocalSymbol? _charLocal;
                private readonly ISymbol? _textSymbol;
                private readonly ILocalSymbol? _iSymbol;
                private readonly IParameterSymbol? _parameterSymbol;

                public Context(SemanticModel semanticModel, ILocalSymbol? charLocal, ISymbol? textSymbol, ILocalSymbol? iSymbol, IParameterSymbol? parameterSymbol, CancellationToken cancellationToken)
                {
                    SemanticModel = semanticModel;
                    _charLocal = charLocal;
                    _textSymbol = textSymbol;
                    _iSymbol = iSymbol;
                    _parameterSymbol = parameterSymbol;
                    CancellationToken = cancellationToken;
                }

                public Context WithinNewMethod(IParameterSymbol parameterSymbol)
                {
                    return new Context(SemanticModel, charLocal: null, textSymbol: null, iSymbol: null, parameterSymbol, CancellationToken);
                }

                public bool IsTestedChar(IOperation operation)
                {
                    if (operation is IConversionOperation conversion && conversion.IsImplicit)
                    {
                        operation = conversion.Operand;
                    }

                    if (operation is ILocalReferenceOperation localReference)
                    {
                        return _charLocal is not null && localReference.Local.Name == _charLocal.Name;
                    }

                    if (operation is IParameterReferenceOperation parameterReference)
                    {
                        return _parameterSymbol is not null && parameterReference.Parameter.Name == _parameterSymbol.Name;
                    }

                    return
                        _textSymbol is not null &&
                        _iSymbol is not null &&
                        IsSpanOrStringIndexerWithIGetterOperation(operation, _textSymbol, _iSymbol);
                }

                public bool Equals(Context other) => throw new InvalidOperationException();

                public override bool Equals(object obj) => throw new InvalidOperationException();

                public override int GetHashCode() => throw new InvalidOperationException();

                public static bool operator ==(Context left, Context right) => left.Equals(right);

                public static bool operator !=(Context left, Context right) => !(left == right);
            }

            private readonly struct Chars : IEquatable<Chars>
            {
                public static BitArray Create() => new(char.MaxValue + 1);

                public bool HasValue => RawValue is not null;

                public BitArray RawValue { get; }

                public Chars(char value, BinaryOperatorKind operatorKind)
                {
                    var bits = RawValue = Create();

                    switch (operatorKind)
                    {
                        case BinaryOperatorKind.Equals:
                            bits.Set(value, true);
                            break;

                        case BinaryOperatorKind.NotEquals:
                            bits.SetAll(true);
                            bits.Set(value, false);
                            break;

                        default:
                            (int start, int end) = operatorKind switch
                            {
                                BinaryOperatorKind.GreaterThan => (value + 1, char.MaxValue),
                                BinaryOperatorKind.GreaterThanOrEqual => (value, char.MaxValue),
                                BinaryOperatorKind.LessThan => (0, value),
                                BinaryOperatorKind.LessThanOrEqual => (0, value + 1),
                                _ => throw new NotSupportedException(operatorKind.ToString())
                            };

                            for (int i = start; i <= end; i++)
                            {
                                bits.Set(i, true);
                            }

                            break;
                    }
                }

                public Chars(char inclusiveStart, char inclusiveEnd)
                {
                    var bits = RawValue = Create();

                    for (int i = inclusiveStart; i <= inclusiveEnd; i++)
                    {
                        bits.Set(i, true);
                    }
                }

                public Chars(string chars)
                {
                    var bits = RawValue = Create();

                    foreach (char c in chars)
                    {
                        bits.Set(c, true);
                    }
                }

                public Chars(BitArray bits)
                {
                    RawValue = bits;
                }

                private BitArray Copy() => new(RawValue);

                public Chars Not() => new(Copy().Not());

                public Chars Or(Chars other) => new(Copy().Or(other.RawValue));

                public Chars And(Chars other) => new(Copy().And(other.RawValue));

                public bool Equals(Chars other) => throw new InvalidOperationException();

                public override bool Equals(object obj) => throw new InvalidOperationException();

                public override int GetHashCode() => throw new InvalidOperationException();

                public static bool operator ==(Chars left, Chars right) => left.Equals(right);

                public static bool operator !=(Chars left, Chars right) => !(left == right);
            }

            private static bool TryGetChars(ref Context context, IOperation? condition, out Chars chars)
            {
                RuntimeHelpers.EnsureSufficientExecutionStack();

                if (context.CancellationToken.IsCancellationRequested)
                {
                    chars = default;
                    return false;
                }

                if (condition is IUnaryOperation unary)
                {
                    return TryGetCharsFromUnaryOperation(ref context, unary, out chars);
                }
                else if (condition is IBinaryOperation binary)
                {
                    return TryGetCharsFromBinaryOperation(ref context, binary, out chars);
                }
                else if (condition is IInvocationOperation invocation)
                {
                    return TryGetCharsFromInvocation(ref context, invocation, out chars);
                }
                else if (condition is IIsPatternOperation isPattern)
                {
                    return TryGetCharsFromIsPatternOperation(ref context, isPattern, out chars);
                }
                else if (condition is ILiteralOperation literal)
                {
                    return TryGetCharsFromLiteral(literal, out chars);
                }

                chars = default;
                return false;
            }

            private static bool TryGetCharsFromUnaryOperation(ref Context context, IUnaryOperation unary, out Chars chars)
            {
                if (unary.OperatorKind == UnaryOperatorKind.Not)
                {
                    if (TryGetChars(ref context, unary.Operand, out chars))
                    {
                        chars = chars.Not();
                        return true;
                    }
                }

                chars = default;
                return false;
            }

            private static bool TryGetCharsFromBinaryOperation(ref Context context, IBinaryOperation binary, out Chars chars)
            {
                if (binary.OperatorKind is
                    BinaryOperatorKind.ConditionalOr or BinaryOperatorKind.Or or
                    BinaryOperatorKind.ConditionalAnd or BinaryOperatorKind.And)
                {
                    if (TryGetChars(ref context, binary.LeftOperand, out Chars left) &&
                        TryGetChars(ref context, binary.RightOperand, out Chars right))
                    {
                        chars = binary.OperatorKind is BinaryOperatorKind.ConditionalAnd or BinaryOperatorKind.And
                            ? left.And(right)
                            : left.Or(right);
                        return true;
                    }
                }
                else if (binary.OperatorKind is
                    BinaryOperatorKind.Equals or
                    BinaryOperatorKind.NotEquals or
                    BinaryOperatorKind.LessThan or
                    BinaryOperatorKind.LessThanOrEqual or
                    BinaryOperatorKind.GreaterThan or
                    BinaryOperatorKind.GreaterThanOrEqual)
                {
                    BinaryOperatorKind operatorKind = binary.OperatorKind;
                    IOperation? otherValue = null;

                    if (context.IsTestedChar(binary.LeftOperand))
                    {
                        otherValue = binary.RightOperand;
                    }
                    else if (context.IsTestedChar(binary.RightOperand))
                    {
                        otherValue = binary.LeftOperand;
                        operatorKind = RotateOperatorIfOrderMatters(operatorKind);
                    }

                    if (IsCharLiteral(otherValue, out char value))
                    {
                        chars = new Chars(value, operatorKind);
                        return true;
                    }

                    if (otherValue is null &&
                        TryGetCharsFromLiteralIndexOfOperation(ref context, binary, out chars))
                    {
                        return true;
                    }

                    if (otherValue is null &&
                        TryGetCharsFromUintRangeCheckOperation(ref context, binary, out chars))
                    {
                        return true;
                    }
                }

                chars = default;
                return false;
            }

            private static bool TryGetCharsFromIsPatternOperation(ref Context context, IIsPatternOperation isPattern, out Chars chars)
            {
                if (context.IsTestedChar(isPattern.Value) &&
                    TryGetCharsFromPattern(isPattern.Pattern, out chars))
                {
                    return true;
                }

                chars = default;
                return false;

                static bool TryGetCharsFromPattern(IPatternOperation pattern, out Chars chars)
                {
                    if (pattern is IConstantPatternOperation constant)
                    {
                        if (IsLiteral(constant.Value, out char value))
                        {
                            chars = new Chars(value, BinaryOperatorKind.Equals);
                            return true;
                        }
                    }
                    else if (pattern is INegatedPatternOperation negated)
                    {
                        if (TryGetCharsFromPattern(negated.Pattern, out chars))
                        {
                            chars = chars.Not();
                            return true;
                        }
                    }
                    else if (pattern is IBinaryPatternOperation binary)
                    {
                        if (binary.OperatorKind is BinaryOperatorKind.And or BinaryOperatorKind.Or)
                        {
                            if (TryGetCharsFromPattern(binary.LeftPattern, out Chars left) &&
                                TryGetCharsFromPattern(binary.RightPattern, out Chars right))
                            {
                                chars = binary.OperatorKind == BinaryOperatorKind.And
                                    ? left.And(right)
                                    : left.Or(right);
                                return true;
                            }
                        }
                    }

                    chars = default;
                    return false;
                }
            }

            private static bool TryGetCharsFromLiteral(ILiteralOperation literal, out Chars chars)
            {
                if (IsLiteral(literal, out bool boolLiteral))
                {
                    var bits = Chars.Create();

                    if (boolLiteral)
                    {
                        bits.SetAll(true);
                    }

                    chars = new Chars(bits);
                    return true;
                }

                chars = default;
                return false;
            }

            private static bool TryGetCharsFromInvocation(ref Context context, IInvocationOperation invocation, out Chars chars)
            {
                IMethodSymbol targetMethod = invocation.TargetMethod;

                if (targetMethod.ReturnType.SpecialType == SpecialType.System_Boolean)
                {
                    if (TryGetCharsFromWellKnownMethod(ref context, invocation, out chars))
                    {
                        return true;
                    }

                    if (targetMethod.IsStatic &&
                        invocation.Arguments.Length == 1 &&
                        context.IsTestedChar(invocation.Arguments[0].Value))
                    {
                        ImmutableArray<SyntaxReference> declaringSyntaxReferences = targetMethod.DeclaringSyntaxReferences;
                        if (declaringSyntaxReferences.Length == 1 &&
                            declaringSyntaxReferences[0].GetSyntax(context.CancellationToken) is { } declaringSyntax &&
                            context.SemanticModel.GetOperation(declaringSyntax, context.CancellationToken) is IMethodBodyOperation methodBody)
                        {
                            ImmutableArray<IOperation> operations = (methodBody.ExpressionBody ?? methodBody.BlockBody)!.Operations;

                            Context methodContext = context.WithinNewMethod(targetMethod.Parameters[0]);

                            return TryGetCharsFromMethodBody(ref methodContext, operations, out chars);
                        }
                    }
                }

                chars = default;
                return false;
            }

            private static bool TryGetCharsFromMethodBody(ref Context context, ImmutableArray<IOperation> operations, out Chars chars)
            {
                if (operations.Length == 1)
                {
                    if (operations[0] is IReturnOperation returnOperation)
                    {
                        return TryGetChars(ref context, returnOperation.ReturnedValue, out chars);
                    }

                    if (operations[0] is ISwitchOperation switchOperation)
                    {
                        return TryGetCharsFromSwitchStatement(ref context, switchOperation, defaultCaseReturnOperation: null, out chars);
                    }
                }
                else if (operations.Length == 2)
                {
                    if (operations[0] is ISwitchOperation switchOperation &&
                        operations[1] is IReturnOperation defaultCaseReturnOperation)
                    {
                        return TryGetCharsFromSwitchStatement(ref context, switchOperation, defaultCaseReturnOperation, out chars);
                    }
                }

                chars = default;
                return false;
            }

            private static bool TryGetCharsFromSwitchStatement(ref Context context, ISwitchOperation switchOperation, IReturnOperation? defaultCaseReturnOperation, out Chars chars)
            {
                chars = default;

                BitArray bits = Chars.Create();
                HashSet<char> charsSeen = new();

                foreach (ISwitchCaseOperation switchCase in switchOperation.Cases)
                {
                    if (switchCase.Body.Length != 1 ||
                        switchCase.Body[0] is not IReturnOperation returnOperation)
                    {
                        return false;
                    }

                    foreach (ICaseClauseOperation clause in switchCase.Clauses)
                    {
                        if (clause is ISingleValueCaseClauseOperation singleValueClause)
                        {
                            if (!IsLiteral(singleValueClause.Value, out char value) ||
                                switchCase.Body.Length != 1 ||
                                !IsLiteral(returnOperation.ReturnedValue, out bool returnValue))
                            {
                                return false;
                            }

                            bits.Set(value, returnValue);
                            charsSeen.Add(value);
                        }
                        else if (clause is IDefaultCaseClauseOperation)
                        {
                            if (defaultCaseReturnOperation is not null)
                            {
                                // What?? Two default cases / unreachable code?
                                return false;
                            }

                            defaultCaseReturnOperation = returnOperation;
                        }
                    }
                }

                if (defaultCaseReturnOperation is not null)
                {
                    if (!TryGetChars(ref context, defaultCaseReturnOperation.ReturnedValue, out Chars defaultChars))
                    {
                        return false;
                    }

                    for (int i = 0; i <= char.MaxValue; i++)
                    {
                        if (defaultChars.RawValue.Get(i) && !charsSeen.Contains((char)i))
                        {
                            Debug.Assert(!bits.Get(i));
                            bits.Set(i, true);
                        }
                    }
                }

                chars = new Chars(bits);
                return true;
            }

            private static bool TryGetCharsFromWellKnownMethod(ref Context context, IInvocationOperation invocation, out Chars chars)
            {
                chars = default;

                if (invocation.Arguments.Length == 0 ||
                    !context.IsTestedChar(invocation.Arguments[0].Value))
                {
                    return false;
                }

                IMethodSymbol method = invocation.TargetMethod;

                if (method.ContainingType.SpecialType == SpecialType.System_Char)
                {
                    const char HIGH_SURROGATE_START = '\ud800';
                    const char HIGH_SURROGATE_END = '\udbff';
                    const char LOW_SURROGATE_START = '\udc00';
                    const char LOW_SURROGATE_END = '\udfff';

                    const string AsciiAlphaLower = "abcdefghijklmnopqrstuvwxyz";
                    const string AsciiAlphaUpper = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
                    const string AsciiHexLettersLower = "abcdef";
                    const string AsciiHexLettersUpper = "ABCDEF";
                    const string AsciiDigits = "0123456789";

                    if (invocation.Arguments.Length == 1)
                    {
                        chars = method.Name switch
                        {
                            "IsAscii" => new Chars((char)0, (char)127),
                            "IsAsciiLetter" => new Chars(AsciiAlphaLower + AsciiAlphaUpper),
                            "IsAsciiLetterLower" => new Chars(AsciiAlphaLower),
                            "IsAsciiLetterUpper" => new Chars(AsciiAlphaUpper),
                            "IsAsciiLetterOrDigit" => new Chars(AsciiAlphaLower + AsciiAlphaUpper + AsciiDigits),
                            "IsAsciiDigit" => new Chars(AsciiDigits),
                            "IsAsciiHexDigit" => new Chars(AsciiHexLettersLower + AsciiHexLettersUpper + AsciiDigits),
                            "IsAsciiHexDigitLower" => new Chars(AsciiHexLettersLower + AsciiDigits),
                            "IsAsciiHexDigitUpper" => new Chars(AsciiHexLettersUpper + AsciiDigits),
                            nameof(char.IsSurrogate) => new Chars(HIGH_SURROGATE_START, LOW_SURROGATE_END),
                            nameof(char.IsLowSurrogate) => new Chars(LOW_SURROGATE_START, LOW_SURROGATE_END),
                            nameof(char.IsHighSurrogate) => new Chars(HIGH_SURROGATE_START, HIGH_SURROGATE_END),
                            _ => default
                        };
                    }
                    else
                    {
                        chars = method.Name switch
                        {
                            "IsBetween" => TryGetCharsFromCharIsBetweenInvocation(invocation),
                            _ => default
                        };
                    }
                }
                else if (method.ContainingType.SpecialType == SpecialType.System_String)
                {
                    if (invocation.Arguments.Length == 1)
                    {
                        if (method.Name == nameof(string.Contains) &&
                            IsConstantStringLiteralOrReference(invocation.Instance, out string? stringLiteral))
                        {
                            chars = new Chars(stringLiteral);
                            return true;
                        }
                    }
                }
                else if (method.ContainingType.Name == "Ascii" && method.ContainingNamespace.Name == "System")
                {
                    if (invocation.Arguments.Length == 1)
                    {
                        chars = method.Name switch
                        {
                            "IsAscii" => new Chars((char)0, (char)127),
                            _ => default
                        };
                    }
                }

                return chars.HasValue;

                static Chars TryGetCharsFromCharIsBetweenInvocation(IInvocationOperation invocation)
                {
                    if (invocation.Arguments.Length == 2 &&
                        IsCharLiteral(invocation.Arguments[0], out char start) &&
                        IsCharLiteral(invocation.Arguments[1], out char end))
                    {
                        return new Chars(start, end);
                    }

                    return default;
                }
            }

            private static bool TryGetCharsFromLiteralIndexOfOperation(ref Context context, IBinaryOperation binary, out Chars chars)
            {
                chars = default;

                BinaryOperatorKind operatorKind = binary.OperatorKind;
                IInvocationOperation? invocation = null;
                IOperation? otherValue = null;

                if (binary.LeftOperand is IInvocationOperation leftInvocation)
                {
                    invocation = leftInvocation;
                    otherValue = binary.RightOperand;
                }
                else if (binary.RightOperand is IInvocationOperation rightInvocation)
                {
                    invocation = rightInvocation;
                    otherValue = binary.LeftOperand;
                    operatorKind = RotateOperatorIfOrderMatters(operatorKind);
                }
                else
                {
                    return false;
                }

                bool minus = false;

                if (otherValue is IUnaryOperation unary && unary.OperatorKind == UnaryOperatorKind.Minus)
                {
                    minus = true;
                    otherValue = unary.Operand;
                }

                if (!IsLiteral(otherValue, out int intValue))
                {
                    return false;
                }

                if (minus)
                {
                    intValue = -intValue;
                }

                bool inverse = false;

                if (intValue == 0 && operatorKind is BinaryOperatorKind.GreaterThanOrEqual or BinaryOperatorKind.LessThan)
                {
                    inverse = operatorKind == BinaryOperatorKind.LessThan;
                }
                else if (intValue == -1 && operatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.LessThanOrEqual or BinaryOperatorKind.GreaterThan)
                {
                    inverse = operatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.LessThanOrEqual;
                }
                else
                {
                    // This comparison doesn't make sense?
                    return false;
                }

                IMethodSymbol targetMethod = invocation.TargetMethod;

                if (targetMethod.ContainingType.SpecialType == SpecialType.System_String &&
                    targetMethod.Name == nameof(string.IndexOf) &&
                    invocation.Arguments.Length == 1 &&
                    context.IsTestedChar(invocation.Arguments[0].Value) &&
                    IsConstantStringLiteralOrReference(invocation.Instance, out string? stringLiteral))
                {
                    chars = new Chars(stringLiteral);

                    if (inverse)
                    {
                        chars = chars.Not();
                    }

                    return true;
                }

                return false;
            }

            // (uint)(c - 'a') <= (uint)('z' - 'a')
            private static bool TryGetCharsFromUintRangeCheckOperation(ref Context context, IBinaryOperation binary, out Chars chars)
            {
                if (binary.OperatorKind is
                    BinaryOperatorKind.GreaterThan or BinaryOperatorKind.GreaterThanOrEqual or
                    BinaryOperatorKind.LessThan or BinaryOperatorKind.LessThanOrEqual)
                {
                    if (IsCast(binary.LeftOperand, SpecialType.System_UInt32, out IOperation? left) &&
                        HasConstantValue(binary.RightOperand, out uint rightValue) &&
                        left is IBinaryOperation leftBinary &&
                        leftBinary.OperatorKind == BinaryOperatorKind.Subtract &&
                        context.IsTestedChar(leftBinary.LeftOperand) &&
                        IsCast(leftBinary.RightOperand, SpecialType.System_Int32, out IOperation? minValueOperation) &&
                        IsLiteral(minValueOperation, out char minValue) &&
                        (long)rightValue + minValue <= char.MaxValue &&
                        minValue > 0)
                    {
                        char maxValue = (char)(rightValue + minValue);
                        chars = binary.OperatorKind switch
                        {
                            BinaryOperatorKind.LessThanOrEqual => new Chars(minValue, maxValue),
                            BinaryOperatorKind.LessThan => new Chars(minValue, (char)(maxValue - 1)),
                            BinaryOperatorKind.GreaterThan => new Chars(minValue, maxValue).Not(),
                            BinaryOperatorKind.GreaterThanOrEqual => new Chars(minValue, (char)(maxValue - 1)).Not(),
                            _ => throw new InvalidOperationException()
                        };
                        return true;
                    }
                }

                chars = default;
                return false;

                static bool IsCast(IOperation operation, SpecialType targetType, [NotNullWhen(true)] out IOperation? innerValue)
                {
                    if (operation is IConversionOperation conversion &&
                        !conversion.IsChecked &&
                        conversion.Conversion.Exists &&
                        conversion.Conversion.IsNumeric &&
                        conversion.Type?.SpecialType == targetType)
                    {
                        innerValue = conversion.Operand;
                        return true;
                    }

                    innerValue = default;
                    return false;
                }
            }

            private static BinaryOperatorKind RotateOperatorIfOrderMatters(BinaryOperatorKind operatorKind)
            {
                return operatorKind switch
                {
                    BinaryOperatorKind.LessThan => BinaryOperatorKind.GreaterThanOrEqual,
                    BinaryOperatorKind.LessThanOrEqual => BinaryOperatorKind.GreaterThan,
                    BinaryOperatorKind.GreaterThan => BinaryOperatorKind.LessThanOrEqual,
                    BinaryOperatorKind.GreaterThanOrEqual => BinaryOperatorKind.LessThan,
                    _ => operatorKind
                };
            }

            private static bool IsCharLiteral(IOperation? operation, out char value)
            {
                if (operation is not null &&
                    operation.ConstantValue.HasValue)
                {
                    if (operation.ConstantValue.Value is char charValue)
                    {
                        value = charValue;
                        return true;
                    }
                    else if (operation.ConstantValue.Value is int intValue)
                    {
                        if (intValue is >= char.MinValue and <= char.MaxValue)
                        {
                            value = (char)intValue;
                            return true;
                        }
                    }
                }

                value = default;
                return false;
            }

            private static bool IsLiteral<T>(IOperation? operation, [MaybeNullWhen(false)] out T value)
            {
                if (operation is ILiteralOperation && HasConstantValue(operation, out value))
                {
                    return true;
                }

                value = default;
                return false;
            }

            private static bool IsConstantStringLiteralOrReference(IOperation? operation, [NotNullWhen(true)] out string? value)
            {
                if (operation is not null &&
                    operation.Type is { SpecialType: SpecialType.System_String } &&
                    operation.ConstantValue.HasValue &&
                    operation is ILiteralOperation or IFieldReferenceOperation or ILocalReferenceOperation &&
                    operation.ConstantValue.Value is string stringValue)
                {
                    value = stringValue;
                    return true;
                }

                value = null;
                return false;
            }

            private static bool HasConstantValue<T>(IOperation operation, [MaybeNullWhen(false)] out T value)
            {
                if (operation.ConstantValue.HasValue &&
                    operation.ConstantValue.Value is T tValue)
                {
                    value = tValue;
                    return true;
                }

                value = default;
                return false;
            }
        }
    }
}