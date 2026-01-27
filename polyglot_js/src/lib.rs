use js_sys::{Object, Reflect};
use polyglot_interpreter::evaluate_boolean_expression;
use std::collections::HashMap;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn evaluate(expression: &str, parameters: &Object) -> bool {
    // jesus christ... this is retarded.
    // we have to store parameters in an owned hashmap because we can't
    // borrow memory from the JS side.
    let parameters = convert_parameters(parameters);
    evaluate_boolean_expression(expression, &parameters).unwrap()
}

fn convert_parameters(parameters: &Object) -> HashMap<String, String> {
    js_sys::Object::keys(parameters)
        .into_iter()
        .filter_map(|key| {
            let v = Reflect::get(parameters, &key).ok()?.as_string()?;
            let k = key.as_string()?;
            Some((k, v))
        })
        .fold(HashMap::default(), |mut acc, (key, value)| {
            acc.insert(key, value);
            acc
        })
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;

    use super::*;

    #[wasm_bindgen_test]
    fn object_with_one_key_is_converted_to_hashmap() {
        let map = Object::new();
        Reflect::set(&map, &"key".into(), &"value".into()).unwrap();
        let result = convert_parameters(&map);
        let mut expected = HashMap::new();
        expected.insert("key".to_string(), "value".to_string());
        assert_eq!(result, expected);
    }

    #[wasm_bindgen_test]
    fn simple_expression_with_parameters_evaluates_to_true() {
        let map = Object::new();
        Reflect::set(&map, &"a".into(), &"1".into()).unwrap();
        let result = evaluate("(= @a 1)", &map);
        assert!(result);
    }

    #[wasm_bindgen_test]
    fn polish_special_characters_in_literals() {
        let map = Object::new();
        let result = evaluate("(= 'Zażółć' 'Zażółć')", &map);
        assert!(result);
    }

    #[wasm_bindgen_test]
    fn polish_special_characters_in_parameters() {
        let map = Object::new();
        Reflect::set(&map, &"greeting".into(), &"Cześć".into()).unwrap();
        let result = evaluate("(= 'Cześć' @greeting)", &map);
        assert!(result);
    }

    #[wasm_bindgen_test]
    fn polish_characters_in_complex_expression() {
        let map = Object::new();
        Reflect::set(&map, &"miasto".into(), &"Łódź".into()).unwrap();
        let result = evaluate("(& (= 'Łódź' @miasto) (= 'polska' 'polska'))", &map);
        assert!(result);
    }
