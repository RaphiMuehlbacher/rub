use crate::builtins::{float_vec_sum_method, vec_len_method};
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
        self.methods.get(base_type)?.get(method_name)
    }

    fn create_method(
        &mut self,
        base_type: &Type,
        method_name: &str,
        params: Vec<Type>,
        return_ty: Type,
        method: fn(Vec<Value>) -> Result<Value, String>,
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
        let vec_string_ty = Type::Vec(Box::new(Type::String));
        let vec_bool_ty = Type::Vec(Box::new(Type::Bool));
        let vec_nil_ty = Type::Vec(Box::new(Type::Nil));

        self.create_method(&vec_float_ty, "len", vec![], Type::Float, vec_len_method);
        self.create_method(&vec_string_ty, "len", vec![], Type::Float, vec_len_method);
        self.create_method(&vec_bool_ty, "len", vec![], Type::Float, vec_len_method);
        self.create_method(&vec_nil_ty, "len", vec![], Type::Float, vec_len_method);

        self.create_method(&vec_float_ty, "sum", vec![], Type::Float, float_vec_sum_method);
    }

    fn register_methods(&mut self) {
        self.register_vec_methods();
    }
}
