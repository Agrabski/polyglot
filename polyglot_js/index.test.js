import evaluate_expression from './index';

test('Basic expression with parameters evaluates correctly', () => {
    const expression = '"(= @a 1)"';
    const parameters = { a: '1' };
    const result = evaluate_expression(expression, parameters);
    expect(result).toBe(true); // Expected result: 2 * 3 + 4 = 10
});

