use crate::builtins::{float_vec_sum_method, int_vec_sum_method, vec_first_method, vec_len_method};
use crate::interpreter::{Function, InterpreterError, Value};
use crate::ir::DefMap;
use crate::type_inferrer::{Type, TypeVarContext};
use miette::SourceSpan;

#[derive(Debug, PartialEq)]
pub struct MethodRegistry<'a> {
    defs: &'a mut DefMap,
    methods: Vec<(Type, String, Type, Function)>, // (receiver_ty, method_name, method_ty, method_impl)
}

impl<'a> MethodRegistry<'a> {
    pub fn new(defs: &'a mut DefMap) -> Self {
        let mut registry = Self { methods: vec![], defs };
        registry.register_methods();
        registry
    }

    pub fn lookup_method(&self, receiver_ty: &Type, method_name: &str, infer_ctx: &mut TypeVarContext) -> Option<(Type, Function)> {
        for (receiver_ty_pattern, name, method_ty, method_def) in &self.methods {
            if name == method_name {
                let instantiated = infer_ctx.instantiate(receiver_ty_pattern);
                if infer_ctx.unify(&instantiated, receiver_ty, &SourceSpan::from(0)).is_ok() {
                    let instantiated_method_ty = infer_ctx.instantiate(method_ty);
                    return Some((instantiated_method_ty, method_def.clone()));
                }
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
        self.defs.insert_placeholder_function(method_name, 0, SourceSpan::from(0));

        let method_type = Type::Function {
            params,
            return_type: Box::new(return_ty),
        };

        self.methods.push((
            base_type.clone(),
            method_name.to_string(),
            method_type,
            Function::NativeFunction(method),
        ));
    }

    fn register_vec_methods(&mut self) {
        let vec_float_ty = Type::Vec { ty: Box::new(Type::Float) };
        let vec_int_ty = Type::Vec { ty: Box::new(Type::Int) };
        let vec_gen_ty = Type::Vec {
            ty: Box::new(Type::TypeParam(5)),
        };
        self.create_method(&vec_float_ty, "sum", vec![], Type::Float, float_vec_sum_method);
        self.create_method(&vec_int_ty, "sum", vec![], Type::Int, int_vec_sum_method);

        //TODO: currently only for int vec
        self.create_method(&vec_gen_ty, "len", vec![], Type::Int, vec_len_method);
        self.create_method(&vec_int_ty, "first", vec![], Type::Int, vec_first_method);
    }

    fn register_methods(&mut self) {
        self.register_vec_methods();
    }
}
