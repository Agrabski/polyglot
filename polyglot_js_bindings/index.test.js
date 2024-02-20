import evaluate_expression from './index';

test('Basic expression with parameters evaluates correctly', () => {
    const expression = '(= @a 1)';
    const parameters = { a: '1' };
    const result = evaluate_expression(expression, parameters);
    expect(result).toBe(true);
});

test('Basic expression with constants evaluates correctly', () => {
    const expression = '(= 1 1)';
    const parameters = {};
    const result = evaluate_expression(expression, parameters);
    expect(result).toBe(true);
});

