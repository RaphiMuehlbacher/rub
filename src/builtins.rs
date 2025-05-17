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
