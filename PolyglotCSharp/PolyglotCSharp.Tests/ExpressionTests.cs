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
}