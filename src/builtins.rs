use crate::interpreters::Value;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn clock_native(_args: Vec<Value>) -> Result<Value, String> {
    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
    Ok(Value::Number(now.as_millis() as f64))
}

pub fn print_native(args: Vec<Value>) -> Result<Value, String> {
    let mut text = String::new();
    for arg in args {
        text.push_str(arg.to_printable_value().as_str());
    }

    println!("{text}");
    Ok(Value::Nil)
}

pub fn vec_len_method(args: Vec<Value>) -> Result<Value, String> {
    if let Value::Vec(arr) = &args[0] {
        Ok(Value::Number(arr.borrow().len() as f64))
    } else {
        Err("Expected vec".to_string())
    }
}

pub fn float_vec_sum_method(args: Vec<Value>) -> Result<Value, String> {
    if let Value::Vec(arr) = &args[0] {
        let sum = arr
            .borrow()
            .iter()
            .fold(0.0, |acc, val| if let Value::Number(n) = val { acc + n } else { acc });
        Ok(Value::Number(sum))
    } else {
        Err("Expected float vec".to_string())
    }
}

pub fn vec_first_method(args: Vec<Value>) -> Result<Value, String> {
    if let Value::Vec(arr) = &args[0] {
        if let Some(first) = arr.borrow().first() {
            Ok(first.clone())
        } else {
            Err("No first".to_string())
        }
    } else {
        Err("Expected vec".to_string())
    }
}

pub fn vec_push_method(args: Vec<Value>) -> Result<Value, String> {
    if let [Value::Vec(arr), value] = &args[..] {
        arr.borrow_mut().push(value.clone());
        Ok(Value::Nil)
    } else {
        Err("Expected vec and value".to_string())
    }
}
