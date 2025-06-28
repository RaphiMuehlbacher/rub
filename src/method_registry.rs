use crate::builtins::{float_vec_sum_method, int_vec_sum_method};
use crate::interpreter::{Function, InterpreterError, Value};
use crate::ir::{DefKind, DefMap};
use crate::type_inferrer::Type;
use miette::SourceSpan;
use std::collections::HashMap;

pub struct MethodRegistry<'a> {
    defs: &'a mut DefMap,
    methods: HashMap<Type, HashMap<String, (Type, Function)>>,
}

impl<'a> MethodRegistry<'a> {
    pub fn new(defs: &'a mut DefMap) -> Self {
        let mut registry = Self {
            methods: HashMap::new(),
            defs,
        };
        registry.register_methods();
        registry
    }

    pub fn lookup_method(&self, base_type: &Type, method_name: &str) -> Option<&(Type, Function)> {
        if let Some(methods) = self.methods.get(base_type) {
            if let Some(method) = methods.get(method_name) {
                return Some(method);
            }
        }

        None
    }

    fn create_method(
        &mut self,
        base_type: &Type,
        method_name: &str,
        params: Vec<Type>,
        return_ty: Type,
        method: fn(Vec<Value>) -> Result<Value, InterpreterError>,
    ) {
        self.defs
            .insert(method_name, DefKind::Function, 0, SourceSpan::from(0), None, vec![]);

        let method_type = Type::Function {
            params,
            return_type: Box::new(return_ty),
        };

        self.methods
            .entry(base_type.clone())
            .or_insert_with(HashMap::new)
            .insert(method_name.to_string(), (method_type.clone(), Function::NativeFunction(method)));
    }

    fn register_vec_methods(&mut self) {
        let vec_float_ty = Type::Vec { ty: Box::new(Type::Float) };
        let vec_int_ty = Type::Vec { ty: Box::new(Type::Int) };
        self.create_method(&vec_float_ty, "sum", vec![], Type::Float, float_vec_sum_method);
        self.create_method(&vec_int_ty, "sum", vec![], Type::Int, int_vec_sum_method);
    }

    fn register_methods(&mut self) {
        self.register_vec_methods();
    }
}
