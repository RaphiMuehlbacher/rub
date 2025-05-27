use crate::builtins::{float_vec_sum_method, int_vec_sum_method, vec_first_method, vec_get_method, vec_len_method, vec_push_method};
use crate::error::InterpreterError;
use crate::interpreters::{Function, Value};
use crate::type_inferrer::Type;
use std::collections::HashMap;

pub struct MethodRegistry {
    methods: HashMap<Type, HashMap<String, (Type, Function)>>,
}

impl MethodRegistry {
    pub fn new() -> Self {
        let mut registry = Self { methods: HashMap::new() };
        registry.register_methods();
        registry
    }

    pub fn lookup_method(&self, base_type: &Type, method_name: &str) -> Option<&(Type, Function)> {
        if let Some(methods) = self.methods.get(base_type) {
            if let Some(method) = methods.get(method_name) {
                return Some(method);
            }
        }

        for (type_, methods) in &self.methods {
            if let Some(method) = methods.get(method_name) {
                if self.can_monomorphize(type_, base_type) {
                    return Some(method);
                }
            }
        }

        None
    }

    fn can_monomorphize(&self, generic_type: &Type, concrete_type: &Type) -> bool {
        match (generic_type, concrete_type) {
            (Type::Vec(gen_inner), Type::Vec(_)) => {
                matches!(gen_inner.as_ref(), Type::Generic(_))
            }
            _ => false,
        }
    }

    fn create_method(
        &mut self,
        base_type: &Type,
        method_name: &str,
        params: Vec<Type>,
        return_ty: Type,
        method: fn(Vec<Value>) -> Result<Value, InterpreterError>,
    ) {
        let method_type = Type::Function {
            params,
            return_ty: Box::new(return_ty),
        };

        self.methods
            .entry(base_type.clone())
            .or_insert_with(HashMap::new)
            .insert(method_name.to_string(), (method_type.clone(), Function::NativeFunction(method)));
    }

    fn register_vec_methods(&mut self) {
        let vec_float_ty = Type::Vec(Box::new(Type::Float));
        let vec_int_ty = Type::Vec(Box::new(Type::Int));
        let vec_generic_ty = Type::Vec(Box::new(Type::Generic("T".to_string())));

        self.create_method(&vec_generic_ty, "len", vec![], Type::Int, vec_len_method);
        self.create_method(&vec_generic_ty, "first", vec![], Type::Generic("T".to_string()), vec_first_method);
        self.create_method(&vec_float_ty, "sum", vec![], Type::Float, float_vec_sum_method);
        self.create_method(&vec_int_ty, "sum", vec![], Type::Int, int_vec_sum_method);
        self.create_method(
            &vec_generic_ty,
            "push",
            vec![Type::Generic("T".to_string())],
            Type::Nil,
            vec_push_method,
        );

        self.create_method(
            &vec_generic_ty,
            "get",
            vec![Type::Int],
            Type::Generic("T".to_string()),
            vec_get_method,
        );
    }

    fn register_methods(&mut self) {
        self.register_vec_methods();
    }
}
