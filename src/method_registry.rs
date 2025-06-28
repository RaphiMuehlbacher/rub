use crate::builtins::{float_vec_sum_method, int_vec_sum_method, vec_first_method, vec_get_method, vec_len_method, vec_push_method};
use crate::interpreter::{Function, InterpreterError, Value};
use crate::ir::{DefMap, ResolvedType};
use crate::type_inferrer::Type;
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

        for (type_, methods) in &self.methods {
            if let Some(method) = methods.get(method_name) {
                if self.can_monomorphize(type_, base_type) {
                    return Some(method);
                }
            }
        }

        None
    }

    fn can_monomorphize(&self, generic_type: &ResolvedType, concrete_type: &ResolvedType) -> bool {
        match (generic_type, concrete_type) {
            (ResolvedType::Vec(gen_inner), ResolvedType::Vec(_)) => {
                matches!(gen_inner.as_ref(), ResolvedType::Generic(_))
            }
            _ => false,
        }
    }

    fn create_method(
        &mut self,
        base_type: &ResolvedType,
        method_name: &str,
        params: Vec<ResolvedType>,
        return_ty: ResolvedType,
        method: fn(Vec<Value>) -> Result<Value, InterpreterError>,
    ) {
        let method_def = FunctionDef {
            params,
            return_ty: Box::new(return_ty),
        };
        let def_id = self.defs.fresh_function_id();
        self.defs.functions.insert(def_id, method_def);
        let method_type = ResolvedType::Function { def_id };

        self.methods
            .entry(base_type.clone())
            .or_insert_with(HashMap::new)
            .insert(method_name.to_string(), (method_type.clone(), Function::NativeFunction(method)));
    }

    fn register_vec_methods(&mut self) {
        let vec_float_ty = ResolvedType::Vec(Box::new(ResolvedType::Float));
        let vec_int_ty = ResolvedType::Vec(Box::new(ResolvedType::Int));
        let vec_generic_ty = ResolvedType::Vec(Box::new(ResolvedType::Generic("T".to_string())));

        self.create_method(&vec_generic_ty, "len", vec![], ResolvedType::Int, vec_len_method);
        self.create_method(
            &vec_generic_ty,
            "first",
            vec![],
            ResolvedType::Generic("T".to_string()),
            vec_first_method,
        );
        self.create_method(&vec_float_ty, "sum", vec![], ResolvedType::Float, float_vec_sum_method);
        self.create_method(&vec_int_ty, "sum", vec![], ResolvedType::Int, int_vec_sum_method);
        self.create_method(
            &vec_generic_ty,
            "push",
            vec![ResolvedType::Generic("T".to_string())],
            ResolvedType::Nil,
            vec_push_method,
        );

        self.create_method(
            &vec_generic_ty,
            "get",
            vec![ResolvedType::Int],
            ResolvedType::Generic("T".to_string()),
            vec_get_method,
        );
    }

    fn register_methods(&mut self) {
        self.register_vec_methods();
    }
}
