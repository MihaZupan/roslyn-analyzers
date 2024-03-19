// Copyright (c) Microsoft.  All Rights Reserved.  Licensed under the MIT license.  See License.txt in the project root for license information.

using System;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Testing;
using Xunit;
using VerifyCS = Test.Utilities.CSharpCodeFixVerifier<
    Microsoft.NetCore.CSharp.Analyzers.Performance.CSharpUseIndexOfAnyInsteadOfLoop,
    Microsoft.CodeAnalysis.Testing.EmptyCodeFixProvider>;

namespace Microsoft.NetCore.Analyzers.Performance.UnitTests
{
    public class UseIndexOfAnyInsteadOfLoopTests
    {
        private const string TestSource =
            """
            using System;

            class Test
            {
                public static bool TestMethod(string name)
                {
                    [|for (int i = 0; i < name.Length; i++)
                    {
                        char c = name[i];
                        if (!(CharTest1(c) || c == '.' || c == '-' || c == '_') || CharTest2(name[i]))
                        {
                            return false;
                        }
                    }|]
                    return true;
                }

                static bool CharTest1(char c) => c >= 'a' && c <= 'z' && c != 'q' || c is 'A' or 'B' or 'C';
                
                static bool CharTest2(char c)
                {
                    return c == 'b' && CharTest3(c) && c is not ('a' or 'b' or 'c') and not ('b' or 'c') and ('d' or 'e');
                }

                const string ConstString = "abc";
                
                static bool CharTest3(char c)
                {
                    return "123".IndexOf(c) >= 0 || -1 != "456".IndexOf(c) || CharTest4(c) || CharTest6(c) || !ConstString.Contains(c);
                }

                static bool CharTest4(char c)
                {
                    switch (c)
                    {
                        case 'a':
                        case 'b':
                        case 'c':
                            return true;

                        case 'd':
                            return false;

                        case 'e':
                            return true;
                
                        default:
                            return CharTest1(c);
                    }
                }

                static bool CharTest5(char c)
                {
                    switch (c)
                    {
                        case 'a':
                        case 'b':
                        case 'c':
                            return true;
                    }
                
                    return false;
                }

                static bool CharTest6(char c)
                {
                    return
                        (uint)(c - 'a') <= (uint)('z' - 'a') &&
                        (uint)(c - 'a') > 42 &&
                        char.IsAsciiLetterLower(c);
                }
            }
            """;

        [Fact]
        public async Task TestMethod1()
        {
            await VerifyAnalyzerAsync(TestSource);
        }

        [Fact]
        public async Task TestMethod2()
        {
            await VerifyAnalyzerAsync(TestSource.Replace("string name", "ReadOnlySpan<char> name", StringComparison.Ordinal));
        }

        [Fact]
        public async Task TestMethod3()
        {
            await VerifyAnalyzerAsync(TestSource.Replace("string name", "Span<char> name", StringComparison.Ordinal));
        }

        [Fact]
        public async Task TestMethod4()
        {
            const string TestSource =
                """
                using System;
                
                class Test
                {
                    public static bool TestMethod(string name)
                    {
                        [|foreach (char c in name)
                        {
                            if (CharTest1(c))
                            {
                                throw new Exception();
                            }
                        }|]
                        return true;
                    }
                
                    static bool CharTest1(char c) => char.IsSurrogate(c);
                }
                """;

            await VerifyAnalyzerAsync(TestSource);
        }

        [Fact]
        public async Task TestMethod5()
        {
            const string TestSource =
                """
                using System;
                
                class Test
                {
                    public static bool TestMethod(string name)
                    {
                        int i = 0;
                        [|while (i < name.Length)
                        {
                            char c = name[i];
                            if (CharTest1(c))
                            {
                                throw new Exception();
                            }
                            i++;
                        }|]
                        return true;
                    }
                
                    static bool CharTest1(char c) => char.IsSurrogate(c);
                }
                """;

            await VerifyAnalyzerAsync(TestSource);
        }

        private static async Task VerifyAnalyzerAsync(string source) =>
            await VerifyCodeFixAsync(LanguageVersion.CSharp11, source, expected: null);

        private static async Task VerifyCodeFixAsync(LanguageVersion languageVersion, string source, string expected, bool topLevelStatements = false)
        {
            await new VerifyCS.Test
            {
                ReferenceAssemblies = Net80,
                LanguageVersion = languageVersion,
                TestCode = source,
                FixedCode = expected,
                TestState = { OutputKind = topLevelStatements ? OutputKind.ConsoleApplication : null },
            }.RunAsync();
        }

        // TEMP - need newer version of Microsoft.CodeAnalysis.Analyzer.Testing
        // Replace with 'ReferenceAssemblies.Net.Net80'
        private static readonly Lazy<ReferenceAssemblies> _lazyNet80 =
            new(() =>
            {
                if (!NuGet.Frameworks.NuGetFramework.Parse("net8.0").IsPackageBased)
                {
                    // The NuGet version provided at runtime does not recognize the 'net8.0' target framework
                    throw new NotSupportedException("The 'net8.0' target framework is not supported by this version of NuGet.");
                }

                return new ReferenceAssemblies(
                    "net8.0",
                    new PackageIdentity(
                        "Microsoft.NETCore.App.Ref",
                        "8.0.0-preview.7.23375.6"),
                    System.IO.Path.Combine("ref", "net8.0"));
            });

        public static ReferenceAssemblies Net80 => _lazyNet80.Value;
    }
}
