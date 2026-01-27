namespace PolyglotCSharp.Tests;

public class ExpressionTests
{
	[Fact]
	public void SimpleExpressionWithOneParameterReturnsTrue()
	{
		Assert.True(
			ExpressionEvaluator.Evaluate(
				"(= @a 1)",
				new()
				{
					["a"] = "1"
				}
			)
		);
	}

	[Fact]
	public void PolishCharactersInLiterals()
	{
		Assert.True(
			ExpressionEvaluator.Evaluate(
				"(= 'Zażółć' 'Zażółć')",
				new()
			)
		);
	}

	[Fact]
	public void PolishSpecialCharactersInParameters()
	{
		Assert.True(
			ExpressionEvaluator.Evaluate(
				"(= 'Cześć' @greeting)",
				new()
				{
					["greeting"] = "Cześć"
				}
			)
		);
	}

	[Fact]
	public void PolishCharactersInComplexExpression()
	{
		Assert.True(
			ExpressionEvaluator.Evaluate(
				"(& (= 'Łódź' @miasto) (= 'polska' 'polska'))",
				new()
				{
					["miasto"] = "Łódź"
				}
			)
		);
	}
}