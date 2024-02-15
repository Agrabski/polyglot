use std::collections::HashMap;

pub trait ParameterDictionary {
    fn get(&self, key: &str) -> Option<&str>;
}

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
            Some(op @ ('=' | '!')) => {
                let (left, index) = parse_operand(&expression[2..], parameters)?;
                let (right, last_index) = parse_operand(&expression[index + 3..], parameters)?;
                match op {
                    '=' => Some((left == right, last_index)),
                    '!' => Some((left != right, last_index)),
                    _ => None,
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
                        parameters.get(&sub_expression[..end_index]).unwrap_or(&""),
                        end_index + start_index + 1,
                    )
                })
            }
            Some(char) => {
                if char.is_ascii_digit() {
                    let sub_expression = &expression[start_index..];
                    let end_index = sub_expression
                        .chars()
                        .position(|c| !c.is_ascii_digit())
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
}
