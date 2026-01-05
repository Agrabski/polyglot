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
                let (right, last_index) = parse_operand(&expression[index + 3..], parameters)?;
                // include the closing ')' (and possible trailing delimiter) in the computed length
                let expression_length = 5 + index + last_index;
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

        let expr2="  'xyz')";
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
}
