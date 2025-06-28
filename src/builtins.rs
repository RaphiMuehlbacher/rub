use crate::error::RuntimeError::IndexOutOfBounds;
use crate::interpreter::InterpreterError;
use crate::interpreter::Value;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn clock_native(_args: Vec<Value>) -> Result<Value, InterpreterError> {
    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
    Ok(Value::Float(now.as_millis() as f64))
}

pub fn print_native(args: Vec<Value>) -> Result<Value, InterpreterError> {
    let mut text = String::new();
    for arg in args {
        text.push_str(arg.to_printable_value().as_str());
    }

    println!("{text}");
    Ok(Value::Nil)
}

pub fn vec_len_method(args: Vec<Value>) -> Result<Value, InterpreterError> {
    let Value::Vec(arr) = &args[0] else { unreachable!() };
    Ok(Value::Int(arr.borrow().len() as i64))
}

pub fn float_vec_sum_method(args: Vec<Value>) -> Result<Value, InterpreterError> {
    let Value::Vec(arr) = &args[0] else { unreachable!() };
    let sum = arr
        .borrow()
        .iter()
        .fold(0.0, |acc, val| if let Value::Float(n) = val { acc + n } else { acc });
    Ok(Value::Float(sum))
}

pub fn int_vec_sum_method(args: Vec<Value>) -> Result<Value, InterpreterError> {
    let Value::Vec(arr) = &args[0] else { unreachable!() };
    let sum = arr
        .borrow()
        .iter()
        .fold(0, |acc, val| if let Value::Int(n) = val { acc + n } else { acc });
    Ok(Value::Int(sum))
}

pub fn vec_first_method(args: Vec<Value>) -> Result<Value, InterpreterError> {
    let Value::Vec(arr) = &args[0] else { unreachable!() };
    Ok(arr.borrow().first().cloned().unwrap_or(Value::Nil))
}

pub fn vec_push_method(args: Vec<Value>) -> Result<Value, InterpreterError> {
    let [Value::Vec(arr), value] = &args[..] else { unreachable!() };
    arr.borrow_mut().push(value.clone());
    Ok(Value::Nil)
}

pub fn vec_get_method(args: Vec<Value>) -> Result<Value, InterpreterError> {
    let [Value::Vec(arr), Value::Int(index)] = &args[..] else {
        unreachable!()
    };
    let index = *index as usize;
    let arr = arr.borrow();
    if index >= arr.len() {
        return Err(InterpreterError::RuntimeError(IndexOutOfBounds {
            src: String::new(),
            span: 0.into(),
            index,
            length: arr.len(),
        }));
    }
    Ok(arr[index].clone())
}
