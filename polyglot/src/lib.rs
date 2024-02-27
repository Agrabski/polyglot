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
                match op {
                    EQUAL_OPERATOR => Some((left == right, last_index)),
                    NOT_EQUAL_OPERATOR => Some((left != right, last_index)),
                    _ => compare_numeric_values(op, left, right).map(|v| (v, last_index)),
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
                while let Some((result, index)) = eval_internal(current_sub_expression, parameters)
                {
                    r = combine(r, result);
                    current_sub_expression = &current_sub_expression[index..];
                    final_index += index;
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
                    .map(|end_index| (&sub_expression[..end_index], end_index + start_index + 1))
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
}
