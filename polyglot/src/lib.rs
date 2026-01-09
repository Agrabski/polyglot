use std::collections::HashMap;

pub trait ParameterDictionary {
    fn get(&self, key: &str) -> Option<&str>;
}

pub const EQUAL_OPERATOR: char = '=';
pub const NOT_EQUAL_OPERATOR: char = '!';
pub const GREATER_THAN_OPERATOR: char = '>';
pub const GREATER_EQUAL_THAN_OPERATOR: char = ']';
pub const LESS_THAN_OPERATOR: char = '<';
pub const LESS_EQUAL_THAN_OPERATOR: char = '[';

pub fn evaluate_boolean_expression<TParams: ParameterDictionary>(
    expression: &str,
    parameters: &TParams,
) -> Option<bool> {
    eval_internal(expression, parameters).map(|v| v.0)
}

fn eval_internal<TParams: ParameterDictionary>(
    expression: &str,
    parameters: &TParams,
) -> Option<(bool, usize)> {
    let expression = expression.trim();
    match expression.chars().next() {
        Some('(') => match expression.chars().nth(1) {
            None => None,
            Some(
                op @ (EQUAL_OPERATOR
                | NOT_EQUAL_OPERATOR
                | GREATER_THAN_OPERATOR
                | GREATER_EQUAL_THAN_OPERATOR
                | LESS_THAN_OPERATOR
                | LESS_EQUAL_THAN_OPERATOR),
            ) => {
                let (left, index) = parse_operand(&expression[2..], parameters)?;
                let (right, last_index) = parse_operand(&expression[2 + index..], parameters)?;
                // include the closing ')' (and possible trailing delimiter) in the computed length
                // expression starts with '(<'op> ' so the total length is 2 (for '(<op>') + index + last_index + 1 (for ')')
                let expression_length = 3 + index + last_index;
                match op {
                    EQUAL_OPERATOR => Some((left == right, expression_length)),
                    NOT_EQUAL_OPERATOR => Some((left != right, expression_length)),
                    _ => compare_numeric_values(op, left, right).map(|v| (v, expression_length)),
                }
            }
            Some(op @ ('&' | '|')) => {
                let mut current_sub_expression = &expression[2..];
                let combine = match op {
                    '&' => |a, b| a && b,
                    '|' => |a, b| a || b,
                    _ => unreachable!(),
                };
                let mut r = matches!(op, '&');
                let mut final_index = 2;
                loop {
                    let trimmed = current_sub_expression.trim_start();
                    let leading = current_sub_expression.len() - trimmed.len();
                    if let Some((result, index)) = eval_internal(trimmed, parameters) {
                        r = combine(r, result);
                        current_sub_expression = &current_sub_expression[leading + index..];
                        final_index += leading + index;
                    } else {
                        break;
                    }
                }
                // Include the closing ')' in the final_index
                let trimmed = current_sub_expression.trim_start();
                if trimmed.starts_with(')') {
                    let leading = current_sub_expression.len() - trimmed.len();
                    final_index += leading + 1;
                }
                Some((r, final_index))
            }
            _ => None,
        },
        _ => None,
    }
}

fn compare_numeric_values(op: char, left: &str, right: &str) -> Option<bool> {
    if left.starts_with('-') && right.starts_with('-') {
        let left = &left[1..];
        let right = &right[1..];
        if left.len() == right.len() {
            // If both are negative, we need to compare the values in reverse order
            Some(compare_numeric_values_of_equal_length(right, left, op))
        } else {
            Some(
                left.len() > right.len()
                    && (op == GREATER_THAN_OPERATOR || op == GREATER_EQUAL_THAN_OPERATOR)
                    || left.len() < right.len()
                        && (op == LESS_THAN_OPERATOR || op == LESS_EQUAL_THAN_OPERATOR),
            )
        }
    } else if left.starts_with('-') {
        Some(op == LESS_THAN_OPERATOR || op == LESS_EQUAL_THAN_OPERATOR)
    } else if right.starts_with('-') {
        Some(op == GREATER_THAN_OPERATOR || op == GREATER_EQUAL_THAN_OPERATOR)
    } else if left.len() == right.len() {
        Some(compare_numeric_values_of_equal_length(left, right, op))
    } else {
        Some(
            left.len() > right.len()
                && (op == GREATER_THAN_OPERATOR || op == GREATER_EQUAL_THAN_OPERATOR)
                || left.len() < right.len()
                    && (op == LESS_THAN_OPERATOR || op == LESS_EQUAL_THAN_OPERATOR),
        )
    }
}

fn compare_numeric_values_of_equal_length(left: &str, right: &str, op: char) -> bool {
    for (l, r) in left.chars().zip(right.chars()) {
        if l != r {
            return match op {
                GREATER_THAN_OPERATOR => l > r,
                GREATER_EQUAL_THAN_OPERATOR => l >= r,
                LESS_THAN_OPERATOR => l < r,
                LESS_EQUAL_THAN_OPERATOR => l <= r,
                _ => panic!("Invalid operator"),
            };
        }
    }
    op == GREATER_EQUAL_THAN_OPERATOR || op == LESS_EQUAL_THAN_OPERATOR
}

fn parse_operand<'a, TParams: ParameterDictionary>(
    expression: &'a str,
    parameters: &'a TParams,
) -> Option<(&'a str, usize)> {
    let start_index = expression.chars().position(|c| !c.is_whitespace());
    match start_index {
        None => None,
        Some(start_index) => match expression.chars().nth(start_index) {
            Some(')') => None,
            Some('\'') => {
                let sub_expression = &expression[start_index + 1..];
                let end_index = sub_expression.chars().position(|c| c == '\'');
                end_index
                    .map(|end_index| (&sub_expression[..end_index], end_index + start_index + 2))
            }
            Some('@') => {
                let sub_expression = &expression[start_index + 1..];
                let end_index = sub_expression
                    .chars()
                    .position(|c| c.is_whitespace() || c == ')');
                end_index.map(|end_index| {
                    (
                        parameters.get(&sub_expression[..end_index]).unwrap_or(""),
                        end_index + start_index + 1,
                    )
                })
            }
            Some(char) => {
                if char.is_ascii_digit() || char == '-' {
                    let sub_expression = &expression[start_index..];
                    let end_index = sub_expression
                        .chars()
                        .position(|c| !c.is_ascii_digit() && c != '-')
                        .unwrap_or(expression.len());
                    Some((&sub_expression[..end_index], end_index + start_index))
                } else {
                    None
                }
            }

            _ => None,
        },
    }
}

impl ParameterDictionary for HashMap<String, String> {
    fn get(&self, key: &str) -> Option<&str> {
        self.get(key).map(|s| s.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn simple_comparison_of_constant_integers_evaluates_to_true() {
        let parameters = HashMap::new();
        assert!(evaluate_boolean_expression("(= 1 1)", &parameters).unwrap());
    }

    #[test]
    pub fn simple_comparison_of_constant_integers_evaluates_to_false() {
        let parameters = HashMap::new();
        assert!(!evaluate_boolean_expression("(= 1 2)", &parameters).unwrap());
    }

    #[test]
    pub fn simple_not_equal_comparison_of_constant_integers_evaluates_to_true() {
        let parameters = HashMap::new();
        assert!(evaluate_boolean_expression("(! 1 2)", &parameters).unwrap());
    }

    #[test]
    pub fn simple_comparison_of_constant_strings_evaluates_to_true() {
        let parameters = HashMap::new();
        assert!(evaluate_boolean_expression("(= 'a' 'a')", &parameters).unwrap());
    }

    #[test]
    pub fn simple_or_condition_evaluates_to_true() {
        let parameters = HashMap::new();
        assert!(evaluate_boolean_expression("(| (= 'a' 'a') (= 1 2))", &parameters).unwrap());
    }

    #[test]
    pub fn simple_or_condition_evaluates_to_false() {
        let parameters = HashMap::new();
        assert!(!evaluate_boolean_expression("(| (= 'bas' 'a') (= 1 2))", &parameters).unwrap());
    }

    #[test]
    pub fn simple_or_condition_with_second_true_operand_evaluates_to_true() {
        let parameters = HashMap::new();
        assert!(evaluate_boolean_expression(
            "(| (= 'dev' 'test') (= 'test' 'test') (= 'prod' 'test'))",
            &parameters
        )
        .unwrap());
    }

    #[test]
    pub fn simple_and_condition_evaluates_to_true() {
        let parameters = HashMap::new();
        assert!(evaluate_boolean_expression("(& (= 'a' 'a') (= 1 1))", &parameters).unwrap());
    }

    #[test]
    pub fn comparing_parameter_with_literal_returns_true() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        assert!(evaluate_boolean_expression("(= '1' @a)", &parameters).unwrap());
    }

    #[test]
    pub fn comparison_operator_compares_integers_correctly_with_string_literal_syntax() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        assert!(evaluate_boolean_expression("(> '111' @a)", &parameters).unwrap());
    }

    #[test]
    pub fn comparison_operator_compares_negative_integers_correctly_with_string_literal_syntax() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        assert!(!evaluate_boolean_expression("(> '-111' @a)", &parameters).unwrap());
    }

    #[test]
    pub fn comparison_operator_compares_negative_integers_correctly_with_numeric_literal_syntax() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        assert!(!evaluate_boolean_expression("(> -111 @a)", &parameters).unwrap());
    }

    #[test]
    pub fn comparison_operator_compares_two_negative_integers_correctly_with_numeric_literal_syntax(
    ) {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "-110".to_string());
        assert!(!evaluate_boolean_expression("(> -111 @a)", &parameters).unwrap());
    }

    #[test]
    pub fn less_than_comparison_operator_compares_two_negative_integers_correctly_with_numeric_literal_syntax(
    ) {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "-110".to_string());
        assert!(evaluate_boolean_expression("(< -111 @a)", &parameters).unwrap());
    }

    #[test]
    pub fn greater_equal_operator_correctly_compares_equal_numbers() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "-111".to_string());
        let r = evaluate_boolean_expression("(] -111 @a)", &parameters);
        assert!(r.unwrap());
    }

    #[test]
    pub fn negative_number_is_smaller_than_positive_number_of_shorter_length() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "11".to_string());
        assert!(evaluate_boolean_expression("(< -111 @a)", &parameters).unwrap());
    }

    #[test]
    pub fn parse_operand_returns_none_for_empty_expression() {
        let parameters = HashMap::new();
        assert!(parse_operand("", &parameters).is_none());
        assert!(parse_operand("   ", &parameters).is_none());
    }

    #[test]
    pub fn parse_operand_returns_none_for_closing_paren() {
        let parameters = HashMap::new();
        assert!(parse_operand(")", &parameters).is_none());
        assert!(parse_operand(" )", &parameters).is_none());
    }

    #[test]
    pub fn parse_operand_parses_quoted_string_and_index() {
        let parameters = HashMap::new();
        let expr = "'abc' rest";
        let (s, idx) = parse_operand(expr, &parameters).unwrap();
        assert_eq!(s, "abc");
        assert_eq!(expr[idx..], *" rest");

        let expr2 = "  'xyz')";
        let (s2, idx2) = parse_operand(expr2, &parameters).unwrap();
        assert_eq!(s2, "xyz");
        assert_eq!(expr2[idx2..], *")");
    }

    #[test]
    pub fn parse_operand_parses_parameter_and_unknown_returns_empty() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "val".to_string());
        let (s, idx) = parse_operand("@a)", &parameters).unwrap();
        assert_eq!(s, "val");
        assert_eq!(idx, 2);
        let (s2, idx2) = parse_operand("@missing )", &parameters).unwrap();
        assert_eq!(s2, "");
        assert_eq!(idx2, 8);
    }

    #[test]
    pub fn parse_operand_parses_numeric_literals() {
        let parameters = HashMap::new();
        let (s, idx) = parse_operand("123abc", &parameters).unwrap();
        assert_eq!(s, "123");
        assert_eq!(idx, 3);
        let (s2, idx2) = parse_operand("-45 )", &parameters).unwrap();
        assert_eq!(s2, "-45");
        assert_eq!(idx2, 3);
        let (s3, idx3) = parse_operand("-999", &parameters).unwrap();
        assert_eq!(s3, "-999");
        assert_eq!(idx3, 4);
    }

    #[test]
    pub fn complex_and_or_expression_evaluates_correctly_with_param() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        let expr = "(& (| (= 'dev' 'test') (= 'prod' 'test') (= 'testx' 'test')) (= '1' @param))";
        // The OR should be false, and the final result therefore false
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn inner_or_expression_evaluates_to_false() {
        let parameters = HashMap::new();
        let expr = "(| (= 'dev' 'test') (= 'prod' 'test') (= 'testx' 'test'))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn and_with_first_false_second_true_evaluates_to_false() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        assert!(
            !evaluate_boolean_expression("(& (= 'a' 'b') (= '1' @param))", &parameters).unwrap()
        );
    }

    #[test]
    pub fn and_with_inner_or_of_two_false_operands_evaluates_to_false() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        let expr = "(& (| (= 'a' 'b') (= 'c' 'd')) (= '1' @param))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn inner_or_two_false_evaluates_false() {
        let parameters = HashMap::new();
        let expr = "(| (= 'a' 'b') (= 'c' 'd'))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
        // also verify eval_internal on the same literal
        if let Some((v, idx)) = eval_internal(expr, &parameters) {
            assert!(!v);
            assert!(idx > 0);
        } else {
            panic!("eval_internal failed on standalone inner OR");
        }
    }

    #[test]
    pub fn eval_internal_parsing_of_nested_or_in_and_looks_correct() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        let expr = "(& (| (= 'a' 'b') (= 'c' 'd')) (= '1' @param))";
        let current_sub_expression = &expr[2..];
        let trimmed = current_sub_expression.trim_start();
        let leading = current_sub_expression.len() - trimmed.len();
        if let Some((inner_result, index)) = eval_internal(trimmed, &parameters) {
            // Print debug info first

            // inner_result should be false
            assert!(!inner_result, "inner_result unexpectedly true");
            // verify evaluate_boolean_expression on the same trimmed string
            assert!(!evaluate_boolean_expression(trimmed, &parameters).unwrap());
            // the remaining slice after consuming the inner expression should start with a space and then ')'
            // because eval_internal now includes the closing ')' in the returned index
            let rest = &current_sub_expression[leading + index..];
            assert!(
                rest.trim_start().starts_with(')')
                    || rest.is_empty()
                    || rest.trim_start().starts_with('(')
            );
            // Verify that the inner OR actually parsed its subexpressions correctly by
            // parsing the first sub-expression directly from the trimmed inner OR's body
            let inner_or_body = &trimmed[2..];
            let first_sub = inner_or_body.trim_start();
            if let Some((first_result, first_index)) = eval_internal(first_sub, &parameters) {
                assert!(!first_result, "first inner equality unexpectedly true");
                let rest_after_first = &first_sub[first_index..];
                if let Some((second_result, _)) =
                    eval_internal(rest_after_first.trim_start(), &parameters)
                {
                    assert!(!second_result, "second inner equality unexpectedly true");
                } else {
                    panic!("failed to parse second equality inside inner OR");
                }
            } else {
                panic!("failed to parse first equality inside inner OR");
            }
        } else {
            panic!("eval_internal failed to parse nested OR");
        }

        // Check behavior of parsing a single equality followed by another operand in a larger string
        let s = "(= 'a' 'b') (= '1' @param))";
        if let Some((v, idx)) = eval_internal(s, &parameters) {
            assert!(!v);
            // after consuming the equality, remaining string should start with '(' for next operand
            assert!(s[idx..].trim_start().starts_with('('));
        } else {
            panic!("eval_internal failed on equality followed by other operand");
        }
    }

    // Additional regression tests for nested and/or combinations and parameter cases
    #[test]
    pub fn nested_or_with_whitespace_and_param_evaluates_false() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        let expr = "(& (|  (= 'dev'  'test')\n      (= 'prod' 'test')   (= 'testx'  'test' ) )  (= '1' @param))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn nested_or_inner_true_allows_and_true() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        // inner OR has a true equality, and right side equals param
        let expr = "(& (| (= 'dev' 'test') (= 'prod' 'test') (= 'test' 'test')) (= '1' @param))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn nested_deep_or_evaluates_false() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        let expr = "(& (| (| (= 'a' 'b') (= 'c' 'd')) (= 'e' 'f')) (= '1' @param))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn and_or_mixed_true_and_false_variants() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        parameters.insert("b".to_string(), "2".to_string());
        let expr_true = "(& (= '1' @a) (| (= 'x' 'y') (= '2' @b)))";
        assert!(evaluate_boolean_expression(expr_true, &parameters).unwrap());

        // change b so the OR is false
        parameters.insert("b".to_string(), "3".to_string());
        let expr_false = "(& (= '1' @a) (| (= 'x' 'y') (= '2' @b)))";
        assert!(!evaluate_boolean_expression(expr_false, &parameters).unwrap());
    }

    #[test]
    pub fn or_many_operands_true_and_false() {
        let parameters = HashMap::new();
        let expr_true = "(| (= 'a' 'b') (= 'c' 'd') (= 'e' 'f') (= 'g' 'g'))";
        assert!(evaluate_boolean_expression(expr_true, &parameters).unwrap());
        let expr_false = "(| (= 'a' 'b') (= 'c' 'd') (= 'e' 'f'))";
        assert!(!evaluate_boolean_expression(expr_false, &parameters).unwrap());
    }

    #[test]
    pub fn param_missing_in_or_behaviour() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        let expr = "(| (= '1' @a) (= '2' @missing))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
        // remove a
        parameters.clear();
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn complex_and_with_nested_or_and_param_evaluates_to_false() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "2".to_string());
        // (= 'dev' 'test') => false
        // (= 'test' 'test') => true
        // (| false true) => true
        // (= '1' @param) with param=2 => (= '1' '2') => false
        // (& true false) => false
        let expr = "(& (| (= 'dev' 'test') (= 'test' 'test')) (= '1' @param))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn complex_and_with_nested_or_and_matching_param_evaluates_to_true() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        // (= 'dev' 'test') => false
        // (= 'test' 'test') => true
        // (| false true) => true
        // (= '1' @param) with param=1 => (= '1' '1') => true
        // (& true true) => true
        let expr = "(& (| (= 'dev' 'test') (= 'test' 'test')) (= '1' @param))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn complex_and_with_all_false_or_operands() {
        let mut parameters = HashMap::new();
        parameters.insert("param".to_string(), "1".to_string());
        // (= 'dev' 'test') => false
        // (= 'prod' 'test') => false
        // (= 'staging' 'test') => false
        // (| false false false) => false
        // (= '1' @param) => true
        // (& false true) => false
        let expr = "(& (| (= 'dev' 'test') (= 'prod' 'test') (= 'staging' 'test')) (= '1' @param))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn complex_and_with_multiple_or_operands_one_true() {
        let mut parameters = HashMap::new();
        parameters.insert("env".to_string(), "prod".to_string());
        // (= 'dev' @env) with env=prod => false
        // (= 'staging' @env) with env=prod => false
        // (= 'prod' @env) with env=prod => true
        // (| false false true) => true
        // (= '1' '1') => true
        // (& true true) => true
        let expr = "(& (| (= 'dev' @env) (= 'staging' @env) (= 'prod' @env)) (= '1' '1'))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn complex_and_with_matching_param_first_true_second_false() {
        let mut parameters = HashMap::new();
        parameters.insert("status".to_string(), "active".to_string());
        // (= 'active' @status) with status=active => true
        // (= 'inactive' @status) with status=active => false
        // (| true false) => true
        // (= '0' '1') => false
        // (& true false) => false
        let expr = "(& (| (= 'active' @status) (= 'inactive' @status)) (= '0' '1'))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn nested_and_inside_or_with_params() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        parameters.insert("b".to_string(), "2".to_string());
        // (& (= '1' @a) (= '2' @b)) => (& true true) => true
        // (= 'x' 'y') => false
        // (| true false) => true
        let expr = "(| (& (= '1' @a) (= '2' @b)) (= 'x' 'y'))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn nested_and_inside_or_with_params_all_false() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "5".to_string());
        parameters.insert("b".to_string(), "9".to_string());
        // (& (= '1' @a) (= '2' @b)) => (& false false) => false
        // (= 'x' 'y') => false
        // (| false false) => false
        let expr = "(| (& (= '1' @a) (= '2' @b)) (= 'x' 'y'))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn deeply_nested_or_with_multiple_params() {
        let mut parameters = HashMap::new();
        parameters.insert("env".to_string(), "staging".to_string());
        parameters.insert("debug".to_string(), "true".to_string());
        // (| (= 'dev' @env) (= 'staging' @env)) => (| false true) => true
        // (= 'true' @debug) => true
        // (& true true) => true
        let expr = "(& (| (= 'dev' @env) (= 'staging' @env)) (= 'true' @debug))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn deeply_nested_or_with_multiple_params_second_param_false() {
        let mut parameters = HashMap::new();
        parameters.insert("env".to_string(), "staging".to_string());
        parameters.insert("debug".to_string(), "false".to_string());
        // (| (= 'dev' @env) (= 'staging' @env)) => (| false true) => true
        // (= 'true' @debug) with debug=false => false
        // (& true false) => false
        let expr = "(& (| (= 'dev' @env) (= 'staging' @env)) (= 'true' @debug))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn and_with_or_containing_three_params() {
        let mut parameters = HashMap::new();
        parameters.insert("x".to_string(), "10".to_string());
        parameters.insert("y".to_string(), "20".to_string());
        parameters.insert("z".to_string(), "30".to_string());
        // (| (= '10' @x) (= '10' @y) (= '10' @z)) => (| true false false) => true
        // (= '1' '1') => true
        // (& true true) => true
        let expr = "(& (| (= '10' @x) (= '10' @y) (= '10' @z)) (= '1' '1'))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn and_with_or_containing_three_params_no_match() {
        let mut parameters = HashMap::new();
        parameters.insert("x".to_string(), "5".to_string());
        parameters.insert("y".to_string(), "6".to_string());
        parameters.insert("z".to_string(), "7".to_string());
        // (| (= '10' @x) (= '10' @y) (= '10' @z)) => (| false false false) => false
        // (= '1' '1') => true
        // (& false true) => false
        let expr = "(& (| (= '10' @x) (= '10' @y) (= '10' @z)) (= '1' '1'))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn multiple_ands_and_ors_complex_expression() {
        let mut parameters = HashMap::new();
        parameters.insert("role".to_string(), "admin".to_string());
        parameters.insert("active".to_string(), "1".to_string());
        // (| (= 'admin' @role) (= 'superuser' @role)) => true
        // (= '1' @active) => true
        // (& true true) => true
        // (= 'allowed' 'allowed') => true
        // (| true true) => true
        let expr = "(| (& (| (= 'admin' @role) (= 'superuser' @role)) (= '1' @active)) (= 'allowed' 'allowed'))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn complex_expression_with_mixed_literal_and_param_matches() {
        let mut parameters = HashMap::new();
        parameters.insert("tier".to_string(), "premium".to_string());
        // (= 'free' 'free') => true
        // (= 'premium' @tier) with tier=premium => true
        // (| true true) => true
        // (= 'yes' 'yes') => true
        // (& true true) => true
        let expr = "(& (| (= 'free' 'free') (= 'premium' @tier)) (= 'yes' 'yes'))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn three_level_nested_ors() {
        let mut parameters = HashMap::new();
        parameters.insert("env".to_string(), "staging".to_string());
        // (| (= 'dev' @env) (| (= 'staging' @env) (= 'prod' @env))) => (| false (| true false)) => (| false true) => true
        let expr = "(| (= 'dev' @env) (| (= 'staging' @env) (= 'prod' @env)))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn three_level_nested_ands() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        parameters.insert("b".to_string(), "1".to_string());
        // (& (= '1' @a) (& (= '1' @b) (= 'x' 'x'))) => (& true (& true true)) => (& true true) => true
        let expr = "(& (= '1' @a) (& (= '1' @b) (= 'x' 'x')))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn alternating_and_or_left_heavy() {
        let mut parameters = HashMap::new();
        parameters.insert("x".to_string(), "yes".to_string());
        parameters.insert("y".to_string(), "no".to_string());
        // (& (| (= 'yes' @x) (= 'yes' @y)) (= '1' '1'))
        // => (& (| true false) true) => (& true true) => true
        let expr = "(& (| (= 'yes' @x) (= 'yes' @y)) (= '1' '1'))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn alternating_or_and_right_heavy() {
        let mut parameters = HashMap::new();
        parameters.insert("p".to_string(), "1".to_string());
        parameters.insert("q".to_string(), "2".to_string());
        // (| (= '0' '1') (& (= '1' @p) (= '2' @q)))
        // => (| false (& true true)) => (| false true) => true
        let expr = "(| (= '0' '1') (& (= '1' @p) (= '2' @q)))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn four_operand_or_all_false() {
        let parameters = HashMap::new();
        let expr = "(| (= 'a' 'b') (= 'c' 'd') (= 'e' 'f') (= 'g' 'h'))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn four_operand_and_all_true() {
        let parameters = HashMap::new();
        let expr = "(& (= 'a' 'a') (= 'b' 'b') (= 'c' 'c') (= 'd' 'd'))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn four_operand_and_one_false() {
        let parameters = HashMap::new();
        let expr = "(& (= 'a' 'a') (= 'b' 'b') (= 'c' 'd') (= 'e' 'e'))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn nested_or_with_four_branches() {
        let mut parameters = HashMap::new();
        parameters.insert("role".to_string(), "viewer".to_string());
        // (| (= 'admin' @role) (= 'moderator' @role) (= 'editor' @role) (= 'viewer' @role))
        // => (| false false false true) => true
        let expr =
            "(| (= 'admin' @role) (= 'moderator' @role) (= 'editor' @role) (= 'viewer' @role))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn and_of_two_ors_both_true() {
        let mut parameters = HashMap::new();
        parameters.insert("env".to_string(), "prod".to_string());
        parameters.insert("secure".to_string(), "yes".to_string());
        // (& (| (= 'dev' @env) (= 'prod' @env)) (| (= 'no' @secure) (= 'yes' @secure)))
        // => (& (| false true) (| false true)) => (& true true) => true
        let expr = "(& (| (= 'dev' @env) (= 'prod' @env)) (| (= 'no' @secure) (= 'yes' @secure)))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn and_of_two_ors_first_false() {
        let mut parameters = HashMap::new();
        parameters.insert("env".to_string(), "test".to_string());
        parameters.insert("secure".to_string(), "yes".to_string());
        // (& (| (= 'dev' @env) (= 'prod' @env)) (| (= 'no' @secure) (= 'yes' @secure)))
        // => (& (| false false) (| false true)) => (& false true) => false
        let expr = "(& (| (= 'dev' @env) (= 'prod' @env)) (| (= 'no' @secure) (= 'yes' @secure)))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn or_of_two_ands_first_true() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        parameters.insert("b".to_string(), "1".to_string());
        // (| (& (= '1' @a) (= '1' @b)) (& (= '2' @a) (= '2' @b)))
        // => (| (& true true) (& false false)) => (| true false) => true
        let expr = "(| (& (= '1' @a) (= '1' @b)) (& (= '2' @a) (= '2' @b)))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn or_of_three_ands_middle_true() {
        let mut parameters = HashMap::new();
        parameters.insert("x".to_string(), "5".to_string());
        // (| (& (= '1' '2') (= '3' '4')) (& (= '5' @x) (= 'y' 'y')) (& (= 'a' 'b') (= 'c' 'd')))
        // => (| (& false false) (& true true) (& false false)) => (| false true false) => true
        let expr = "(| (& (= '1' '2') (= '3' '4')) (& (= '5' @x) (= 'y' 'y')) (& (= 'a' 'b') (= 'c' 'd')))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn deeply_nested_six_levels() {
        let mut parameters = HashMap::new();
        parameters.insert("flag".to_string(), "true".to_string());
        // (& (| (& (| (= 'a' 'a') (= 'b' 'b')) (= 'c' 'c')) (= 'd' 'd')) (= 'true' @flag))
        // inner OR: (| (= 'a' 'a') (= 'b' 'b')) => (| true true) => true
        // inner AND: (& true (= 'c' 'c')) => (& true true) => true
        // middle OR: (| true (= 'd' 'd')) => (| true true) => true
        // outer AND: (& true (= 'true' @flag)) => (& true true) => true
        let expr =
            "(& (| (& (| (= 'a' 'a') (= 'b' 'b')) (= 'c' 'c')) (= 'd' 'd')) (= 'true' @flag))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn deeply_nested_six_levels_false() {
        let mut parameters = HashMap::new();
        parameters.insert("flag".to_string(), "false".to_string());
        // (& (| (& (| (= 'a' 'a') (= 'b' 'b')) (= 'c' 'c')) (= 'd' 'd')) (= 'true' @flag))
        // inner OR: (| (= 'a' 'a') (= 'b' 'b')) => true
        // inner AND: (& true (= 'c' 'c')) => true
        // middle OR: (| true (= 'd' 'd')) => true
        // outer AND: (& true (= 'true' @flag)) with flag=false => (& true false) => false
        let expr =
            "(& (| (& (| (= 'a' 'a') (= 'b' 'b')) (= 'c' 'c')) (= 'd' 'd')) (= 'true' @flag))";
        assert!(!evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn mixed_params_and_literals_alternating() {
        let mut parameters = HashMap::new();
        parameters.insert("p1".to_string(), "val1".to_string());
        parameters.insert("p2".to_string(), "val2".to_string());
        // (& (| (= 'literal' 'literal') (= 'val1' @p1)) (| (= 'val2' @p2) (= 'other' 'other')))
        // => (& (| true true) (| true true)) => (& true true) => true
        let expr =
            "(& (| (= 'literal' 'literal') (= 'val1' @p1)) (| (= 'val2' @p2) (= 'other' 'other')))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn mixed_params_and_literals_one_param_mismatch() {
        let mut parameters = HashMap::new();
        parameters.insert("p1".to_string(), "val1".to_string());
        parameters.insert("p2".to_string(), "wrong".to_string());
        // (& (| (= 'literal' 'literal') (= 'val1' @p1)) (| (= 'val2' @p2) (= 'other' 'other')))
        // => (& (| true true) (| false true)) => (& true true) => true
        let expr =
            "(& (| (= 'literal' 'literal') (= 'val1' @p1)) (| (= 'val2' @p2) (= 'other' 'other')))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn five_operand_and_with_params() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "1".to_string());
        parameters.insert("b".to_string(), "2".to_string());
        parameters.insert("c".to_string(), "3".to_string());
        // (& (= '1' @a) (= '2' @b) (= '3' @c) (= 'x' 'x') (= 'y' 'y'))
        // => (& true true true true true) => true
        let expr = "(& (= '1' @a) (= '2' @b) (= '3' @c) (= 'x' 'x') (= 'y' 'y'))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn five_operand_or_with_params_last_true() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "5".to_string());
        // (| (= '1' @a) (= '2' @a) (= '3' @a) (= '4' @a) (= '5' @a))
        // => (| false false false false true) => true
        let expr = "(| (= '1' @a) (= '2' @a) (= '3' @a) (= '4' @a) (= '5' @a))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn nested_structure_and_or_and() {
        let mut parameters = HashMap::new();
        parameters.insert("env".to_string(), "staging".to_string());
        // (& (| (= 'dev' @env) (= 'staging' @env)) (& (= 'check1' 'check1') (= 'check2' 'check2')))
        // => (& (| false true) (& true true)) => (& true true) => true
        let expr = "(& (| (= 'dev' @env) (= 'staging' @env)) (& (= 'check1' 'check1') (= 'check2' 'check2')))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn nested_structure_or_and_or() {
        let mut parameters = HashMap::new();
        parameters.insert("role".to_string(), "guest".to_string());
        // (| (& (= 'admin' @role) (= 'verified' 'yes')) (| (= 'guest' @role) (= 'user' @role)))
        // => (| (& false false) (| true false)) => (| false true) => true
        let expr =
            "(| (& (= 'admin' @role) (= 'verified' 'yes')) (| (= 'guest' @role) (= 'user' @role)))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn complex_middle_nesting_with_four_params() {
        let mut parameters = HashMap::new();
        parameters.insert("tier".to_string(), "gold".to_string());
        parameters.insert("active".to_string(), "1".to_string());
        parameters.insert("verified".to_string(), "yes".to_string());
        parameters.insert("age".to_string(), "30".to_string());
        // (& (| (= 'gold' @tier) (= 'platinum' @tier)) (& (= '1' @active) (| (= 'yes' @verified) (= 'no' @verified))))
        // inner OR: (| (= 'yes' @verified) (= 'no' @verified)) => (| true false) => true
        // middle AND: (& (= '1' @active) true) => (& true true) => true
        // first OR: (| (= 'gold' @tier) (= 'platinum' @tier)) => (| true false) => true
        // outer AND: (& true true) => true
        let expr = "(& (| (= 'gold' @tier) (= 'platinum' @tier)) (& (= '1' @active) (| (= 'yes' @verified) (= 'no' @verified))))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn long_chain_ands_with_literal_comparisons() {
        let parameters = HashMap::new();
        // (& (= 'a' 'a') (& (= 'b' 'b') (& (= 'c' 'c') (& (= 'd' 'd') (= 'e' 'e')))))
        // Multiple levels of nested ANDs with all true
        let expr = "(& (= 'a' 'a') (& (= 'b' 'b') (& (= 'c' 'c') (& (= 'd' 'd') (= 'e' 'e')))))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn long_chain_ors_with_last_true() {
        let parameters = HashMap::new();
        // (| (= 'a' 'b') (| (= 'c' 'd') (| (= 'e' 'f') (| (= 'g' 'h') (= 'i' 'i')))))
        // Multiple levels of nested ORs, only last one is true
        let expr = "(| (= 'a' 'b') (| (= 'c' 'd') (| (= 'e' 'f') (| (= 'g' 'h') (= 'i' 'i')))))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn zipper_pattern_alternating_nesting() {
        let mut parameters = HashMap::new();
        parameters.insert("flag1".to_string(), "on".to_string());
        parameters.insert("flag2".to_string(), "off".to_string());
        parameters.insert("flag3".to_string(), "on".to_string());
        // (& (| (= 'on' @flag1) (= 'x' 'y')) (& (= 'off' @flag2) (| (= 'on' @flag3) (= 'z' 'w'))))
        // inner OR: (| (= 'on' @flag3) (= 'z' 'w')) => (| true false) => true
        // inner AND: (& (= 'off' @flag2) true) => (& true true) => true
        // first OR: (| (= 'on' @flag1) (= 'x' 'y')) => (| true false) => true
        // outer AND: (& true true) => true
        let expr = "(& (| (= 'on' @flag1) (= 'x' 'y')) (& (= 'off' @flag2) (| (= 'on' @flag3) (= 'z' 'w'))))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }

    #[test]
    pub fn complex_boolean_with_many_params_mixed_distribution() {
        let mut parameters = HashMap::new();
        parameters.insert("a".to_string(), "alpha".to_string());
        parameters.insert("b".to_string(), "beta".to_string());
        parameters.insert("c".to_string(), "gamma".to_string());
        parameters.insert("d".to_string(), "delta".to_string());
        // (| (& (= 'alpha' @a) (= 'beta' @b)) (& (= 'gamma' @c) (| (= 'delta' @d) (= 'epsilon' 'epsilon'))))
        // left AND: (& true true) => true
        // inner OR: (| (= 'delta' @d) (= 'epsilon' 'epsilon')) => (| true true) => true
        // right AND: (& true true) => true
        // outer OR: (| true true) => true
        let expr = "(| (& (= 'alpha' @a) (= 'beta' @b)) (& (= 'gamma' @c) (| (= 'delta' @d) (= 'epsilon' 'epsilon'))))";
        assert!(evaluate_boolean_expression(expr, &parameters).unwrap());
    }
}
