use crate::interpreters::Value;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn clock_native(_args: Vec<Value>) -> Result<Value, String> {
    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
    Ok(Value::Number(now.as_millis() as f64))
}
