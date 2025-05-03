use crate::interpreters::Value;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn clock_native(_args: Vec<Value>) -> Result<Value, String> {
    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
    Ok(Value::Number(now.as_millis() as f64))
}

pub fn print_native(args: Vec<Value>) -> Result<Value, String> {
    let mut text = String::new();
    for arg in args {
        match arg.to_printable_value() {
            Ok(str) => text.push_str(str.as_str()),
            Err(_) => return Err("error".to_string()),
        }
    }

    println!("{text}");
    Ok(Value::Nil)
}
