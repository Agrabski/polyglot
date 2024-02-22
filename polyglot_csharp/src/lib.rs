use std::collections::HashMap;
uniffi::include_scaffolding!("polyglot_csharp");

use polyglot_interpreter::evaluate_boolean_expression;

pub fn evaluate(expression: &str, parameters: &HashMap<String, String>) -> bool {
    evaluate_boolean_expression(expression, parameters).unwrap_or(false)
}
