use std::collections::HashMap;

use js_sys::Map;
use polyglot::evaluate_boolean_expression;
use wasm_bindgen::prelude::wasm_bindgen;
#[wasm_bindgen(typescript_custom_section)]
const TS_SIGNATURE: &'static str = r#"
export function evaluate(expression: string, parameters: Map<string, string>): boolean;
"#;

pub fn evaluate(expression: &str, parameters: Map) -> bool {
    // jesus christ... this is retarded.
    // we have to store parameters in an owned hashmap because we can't
    // borrow memory from the JS side.
    let parameters = parameters
        .keys()
        .into_iter()
        .flat_map(|key| {
            key.map(|k| {
                let v = parameters.get(&k).as_string()?;
                let key = k.as_string()?;
                Some((key, v))
            })
        })
        .flatten()
        .fold(HashMap::default(), |mut acc, (key, value)| {
            acc.insert(key, value);
            acc
        });
    evaluate_boolean_expression(expression, &parameters).unwrap_or(false)
}
