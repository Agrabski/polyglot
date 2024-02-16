using uniffi.polyglot_csharp;

namespace PolyglotCSharp;

public static class ExpressionEvaluator
{
    public static bool Evaluate(string expression, Dictionary<string, string> parametrs)
    {
        return PolyglotCsharpMethods.Evaluate(expression, parametrs);
    }
}

