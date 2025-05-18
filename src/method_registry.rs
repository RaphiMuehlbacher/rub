use crate::builtins::print_native;
use crate::type_inferrer::Type;
use crate::type_inferrer::Type::TypeVar;
use std::collections::HashMap;

pub struct MethodRegistry {
    methods: HashMap<Type, HashMap<String, Type>>,
}

impl MethodRegistry {
    pub fn new() -> Self {
        let mut registry = Self { methods: HashMap::new() };
        registry.register_methods();
        registry
    }

    pub fn lookup_method(&self, base_type: &Type, method_name: &str) -> Option<&Type> {
        self.methods.get(base_type)?.get(method_name)
    }

    fn create_method(&mut self, base_type: Type, method_name: &str, params: Vec<Type>, return_ty: Type) {
        let method_type = Type::Function {
            params: params.into_iter().map(Box::new).collect(),
            return_ty: Box::new(return_ty),
        };

        self.methods
            .entry(base_type)
            .or_insert_with(HashMap::new)
            .insert(method_name.to_string(), method_type.clone());
    }

    fn register_array_methods(&mut self) {
        let array_ty = Type::Array(Box::new(Type::Float));
        self.create_method(array_ty, "len", vec![], Type::Float);
    }

    fn register_methods(&mut self) {
        self.register_array_methods();
    }
}
