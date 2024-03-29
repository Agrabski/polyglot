import { evaluate } from "polyglot_js/index.js";

/**
 * Evaluates a boolean expression with the given parameters.
 * @param {string} expression - The expression to evaluate.
 * @param {Map<string, string>} parameters - The parameters for the expression.
 * @returns {boolean} - The result of the evaluation.
 */
export default function evaluate_expression(expression, parameters) {
    return evaluate(expression, parameters);
};