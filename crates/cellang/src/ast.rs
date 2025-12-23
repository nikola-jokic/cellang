use crate::env::Env;
use crate::error::{RuntimeError, SyntaxError};
use crate::parser::{Atom, Op, TokenTree};
use crate::types::{FunctionDecl, NamedType, OverloadDecl, Type, TypeName};
use miette::Diagnostic;
use serde::Serialize;
use thiserror::Error;

/// Describes failures that can occur while compiling CEL source into a typed AST.
#[derive(Debug, Error, Diagnostic)]
pub enum CompileError {
	#[error(transparent)]
	#[diagnostic(transparent)]
	Syntax(#[from] SyntaxError),
	#[error(transparent)]
	#[diagnostic(transparent)]
	Type(#[from] RuntimeError),
}

/// Fully typed expression tree produced after semantic analysis.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TypedExpr {
	pub ty: Type,
	pub expr: ExprKind,
}

impl TypedExpr {
	fn new(ty: Type, expr: ExprKind) -> Self {
		Self { ty, expr }
	}
}

/// Logical structure of a typed AST node.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ExprKind {
	Literal(LiteralValue),
	Ident { name: String },
	List { elements: Vec<TypedExpr> },
	Map { entries: Vec<MapEntry> },
	Unary { op: UnaryOp, expr: Box<TypedExpr> },
	Binary { op: BinaryOp, left: Box<TypedExpr>, right: Box<TypedExpr> },
	Call {
		function: String,
		args: Vec<TypedExpr>,
		is_method: bool,
	},
	Field {
		target: Box<TypedExpr>,
		accessor: FieldAccessor,
	},
	Index {
		target: Box<TypedExpr>,
		index: Box<TypedExpr>,
	},
	Ternary {
		condition: Box<TypedExpr>,
		then_branch: Box<TypedExpr>,
		else_branch: Box<TypedExpr>,
	},
	Group { expr: Box<TypedExpr> },
	Dyn { expr: Box<TypedExpr> },
}

/// Describes how a field is accessed (static `foo.bar` vs dynamic `foo[field]`).
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "accessor", rename_all = "snake_case")]
pub enum FieldAccessor {
	Static { name: String },
	Dynamic { expr: Box<TypedExpr> },
}

/// Key/value pair inside a typed map literal.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MapEntry {
	pub key: TypedExpr,
	pub value: TypedExpr,
}

/// Literal payloads captured inside [`ExprKind::Literal`].
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "literal", content = "value", rename_all = "snake_case")]
pub enum LiteralValue {
	Bool(bool),
	Int(i64),
	Uint(u64),
	Double(f64),
	String(String),
	Bytes(Vec<u8>),
	Null,
}

/// Supported unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum UnaryOp {
	Not,
	Neg,
}

/// Supported binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BinaryOp {
	Add,
	Subtract,
	Multiply,
	Divide,
	Modulo,
	And,
	Or,
	Equal,
	NotEqual,
	Less,
	LessEqual,
	Greater,
	GreaterEqual,
	In,
}

/// Performs semantic analysis over the parsed [`TokenTree`] and produces a typed
/// expression graph that can be serialized and cached.
pub fn type_check<'src>(
	env: &Env,
	node: &TokenTree<'src>,
) -> Result<TypedExpr, RuntimeError> {
	infer_expr(env, node)
}

fn infer_expr<'src>(
	env: &Env,
	node: &TokenTree<'src>,
) -> Result<TypedExpr, RuntimeError> {
	match node {
		TokenTree::Atom(atom) => infer_atom(env, atom),
		TokenTree::Cons(op, args) => infer_cons(env, *op, args),
		TokenTree::Call {
			func,
			args,
			is_method,
		} => infer_call(env, func, args, *is_method),
	}
}

fn infer_atom(env: &Env, atom: &Atom<'_>) -> Result<TypedExpr, RuntimeError> {
	let expr = match atom {
		Atom::Bool(value) => TypedExpr::new(
			Type::Bool,
			ExprKind::Literal(LiteralValue::Bool(*value)),
		),
		Atom::Int(value) => TypedExpr::new(
			Type::Int,
			ExprKind::Literal(LiteralValue::Int(*value)),
		),
		Atom::Uint(value) => TypedExpr::new(
			Type::Uint,
			ExprKind::Literal(LiteralValue::Uint(*value)),
		),
		Atom::Double(value) => TypedExpr::new(
			Type::Double,
			ExprKind::Literal(LiteralValue::Double(*value)),
		),
		Atom::String(value) => TypedExpr::new(
			Type::String,
			ExprKind::Literal(LiteralValue::String(value.to_string())),
		),
		Atom::Bytes(value) => TypedExpr::new(
			Type::Bytes,
			ExprKind::Literal(LiteralValue::Bytes(value.to_vec())),
		),
		Atom::Null => TypedExpr::new(Type::Null, ExprKind::Literal(LiteralValue::Null)),
		Atom::Ident(name) => {
			let decl = env
				.lookup_ident(name)
				.ok_or_else(|| RuntimeError::missing_identifier(name))?;
			TypedExpr::new(
				decl.ty.clone(),
				ExprKind::Ident {
					name: (*name).to_string(),
				},
			)
		}
	};
	Ok(expr)
}

fn infer_cons(
	env: &Env,
	op: Op,
	args: &[TokenTree<'_>],
) -> Result<TypedExpr, RuntimeError> {
	match op {
		Op::Group => {
			debug_assert_eq!(args.len(), 1);
			let expr = infer_expr(env, &args[0])?;
			let ty = expr.ty.clone();
			Ok(TypedExpr::new(
				ty,
				ExprKind::Group {
					expr: Box::new(expr),
				},
			))
		}
		Op::List => infer_list_literal(env, args),
		Op::Map => infer_map_literal(env, args),
		Op::Dyn => {
			debug_assert_eq!(args.len(), 1);
			let expr = infer_expr(env, &args[0])?;
			Ok(TypedExpr::new(
				Type::Dyn,
				ExprKind::Dyn {
					expr: Box::new(expr),
				},
			))
		}
		Op::Not => {
			debug_assert_eq!(args.len(), 1);
			let expr = infer_expr(env, &args[0])?;
			expect_boolean(&expr.ty, "logical not")?;
			Ok(TypedExpr::new(
				Type::Bool,
				ExprKind::Unary {
					op: UnaryOp::Not,
					expr: Box::new(expr),
				},
			))
		}
		Op::Minus => {
			if args.len() == 1 {
				let expr = infer_expr(env, &args[0])?;
				let result_ty = numeric_unary_result(&expr.ty, "unary minus")?;
				Ok(TypedExpr::new(
					result_ty,
					ExprKind::Unary {
						op: UnaryOp::Neg,
						expr: Box::new(expr),
					},
				))
			} else {
				debug_assert_eq!(args.len(), 2);
				let left = infer_expr(env, &args[0])?;
				let right = infer_expr(env, &args[1])?;
				let ty = numeric_binary_result(
					&left.ty,
					&right.ty,
					NumericBinaryOp::Subtract,
				)?;
				Ok(make_binary(BinaryOp::Subtract, ty, left, right))
			}
		}
		Op::Plus => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			let ty = infer_addition_type(env, &left.ty, &right.ty)?;
			Ok(make_binary(BinaryOp::Add, ty, left, right))
		}
		Op::Multiply => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			let ty = numeric_binary_result(
				&left.ty,
				&right.ty,
				NumericBinaryOp::Multiply,
			)?;
			Ok(make_binary(BinaryOp::Multiply, ty, left, right))
		}
		Op::Devide => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			let ty = numeric_binary_result(
				&left.ty,
				&right.ty,
				NumericBinaryOp::Divide,
			)?;
			Ok(make_binary(BinaryOp::Divide, ty, left, right))
		}
		Op::Mod => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			let ty = numeric_binary_result(
				&left.ty,
				&right.ty,
				NumericBinaryOp::Modulo,
			)?;
			Ok(make_binary(BinaryOp::Modulo, ty, left, right))
		}
		Op::And => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			expect_boolean(&left.ty, "logical and")?;
			expect_boolean(&right.ty, "logical and")?;
			Ok(make_binary(BinaryOp::And, Type::Bool, left, right))
		}
		Op::Or => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			expect_boolean(&left.ty, "logical or")?;
			expect_boolean(&right.ty, "logical or")?;
			Ok(make_binary(BinaryOp::Or, Type::Bool, left, right))
		}
		Op::EqualEqual => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			Ok(make_binary(BinaryOp::Equal, Type::Bool, left, right))
		}
		Op::NotEqual => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			Ok(make_binary(BinaryOp::NotEqual, Type::Bool, left, right))
		}
		Op::Less | Op::LessEqual | Op::Greater | Op::GreaterEqual => {
			debug_assert_eq!(args.len(), 2);
			let left = infer_expr(env, &args[0])?;
			let right = infer_expr(env, &args[1])?;
			ensure_comparable(&left.ty, &right.ty, op)?;
			let bop = match op {
				Op::Less => BinaryOp::Less,
				Op::LessEqual => BinaryOp::LessEqual,
				Op::Greater => BinaryOp::Greater,
				Op::GreaterEqual => BinaryOp::GreaterEqual,
				_ => unreachable!(),
			};
			Ok(make_binary(bop, Type::Bool, left, right))
		}
		Op::IfTernary => {
			debug_assert_eq!(args.len(), 3);
			let condition = infer_expr(env, &args[0])?;
			expect_boolean(&condition.ty, "ternary condition")?;
			let then_branch = infer_expr(env, &args[1])?;
			let else_branch = infer_expr(env, &args[2])?;
			let ty = unify_types(env, then_branch.ty.clone(), else_branch.ty.clone())?;
			Ok(TypedExpr::new(
				ty,
				ExprKind::Ternary {
					condition: Box::new(condition),
					then_branch: Box::new(then_branch),
					else_branch: Box::new(else_branch),
				},
			))
		}
		Op::In => {
			debug_assert_eq!(args.len(), 2);
			infer_in_operator(env, &args[0], &args[1])
		}
		Op::Index => {
			debug_assert_eq!(args.len(), 2);
			infer_index_access(env, &args[0], &args[1])
		}
		Op::Field => {
			debug_assert_eq!(args.len(), 2);
			infer_field_access(env, &args[0], &args[1])
		}
		Op::Var | Op::For | Op::While | Op::Call => Err(RuntimeError::new(
			format!("Operator '{op:?}' is not supported in this context"),
		)),
	}
}

fn infer_list_literal(
	env: &Env,
	args: &[TokenTree<'_>],
) -> Result<TypedExpr, RuntimeError> {
	if args.is_empty() {
		return Ok(TypedExpr::new(
			Type::list(Type::Dyn),
			ExprKind::List { elements: Vec::new() },
		));
	}
	let mut element_ty = None;
	let mut elements = Vec::with_capacity(args.len());
	for expr in args {
		let typed = infer_expr(env, expr)?;
		element_ty = match element_ty {
			Some(current) => {
				Some(unify_types(env, current, typed.ty.clone())?)
			}
			None => Some(typed.ty.clone()),
		};
		elements.push(typed);
	}
	let elem_ty = element_ty.unwrap_or(Type::Dyn);
	Ok(TypedExpr::new(
		Type::list(elem_ty),
		ExprKind::List { elements },
	))
}

fn infer_map_literal(
	env: &Env,
	args: &[TokenTree<'_>],
) -> Result<TypedExpr, RuntimeError> {
	if !args.len().is_multiple_of(2) {
		return Err(RuntimeError::new(
			"map literal expects key/value pairs but received odd number of expressions",
		));
	}
	if args.is_empty() {
		return Ok(TypedExpr::new(
			Type::map(Type::Dyn, Type::Dyn),
			ExprKind::Map { entries: Vec::new() },
		));
	}
	let mut key_ty = None;
	let mut value_ty = None;
	let mut entries = Vec::with_capacity(args.len() / 2);
	for chunk in args.chunks(2) {
		let key = infer_expr(env, &chunk[0])?;
		let value = infer_expr(env, &chunk[1])?;
		key_ty = match key_ty {
			Some(current) => Some(unify_types(env, current, key.ty.clone())?),
			None => Some(key.ty.clone()),
		};
		value_ty = match value_ty {
			Some(current) => Some(unify_types(env, current, value.ty.clone())?),
			None => Some(value.ty.clone()),
		};
		entries.push(MapEntry { key, value });
	}
	Ok(TypedExpr::new(
		Type::map(key_ty.unwrap(), value_ty.unwrap()),
		ExprKind::Map { entries },
	))
}

fn infer_field_access(
	env: &Env,
	target_expr: &TokenTree<'_>,
	field_expr: &TokenTree<'_>,
) -> Result<TypedExpr, RuntimeError> {
	let target = infer_expr(env, target_expr)?;
	let accessor = if let Some(name) = static_field_name(field_expr) {
		FieldAccessor::Static { name }
	} else {
		FieldAccessor::Dynamic {
			expr: Box::new(infer_expr(env, field_expr)?),
		}
	};
	let ty = match (&target.ty, &accessor) {
		(ty, _) if is_dyn_like(ty) => Type::Dyn,
		(Type::Struct(name), FieldAccessor::Static { name: field }) => {
			struct_field_type(env, name, field)?
		}
		(Type::Struct(_), FieldAccessor::Dynamic { .. }) => Type::Dyn,
		(Type::Map(key_ty, value_ty), FieldAccessor::Static { .. }) => {
			if !is_assignable(&Type::String, key_ty, env) && !is_dyn_like(key_ty) {
				return Err(RuntimeError::new(format!(
					"Map field access requires string keys but found {}",
					describe_type(key_ty)
				)));
			}
			(**value_ty).clone()
		}
		(Type::Map(key_ty, value_ty), FieldAccessor::Dynamic { expr }) => {
			if !is_assignable(key_ty, &expr.ty, env) && !is_dyn_like(&expr.ty) {
				return Err(RuntimeError::new(format!(
					"Map field access expects key type {} but found {}",
					describe_type(key_ty),
					describe_type(&expr.ty)
				)));
			}
			(**value_ty).clone()
		}
		(Type::Null, _) => {
			return Err(RuntimeError::new("Cannot access fields on null"));
		}
		(other, _) => {
			return Err(RuntimeError::new(format!(
				"Field access is not supported on values of kind {}",
				describe_type(other)
			)));
		}
	};
	Ok(TypedExpr::new(
		ty,
		ExprKind::Field {
			target: Box::new(target),
			accessor,
		},
	))
}

fn infer_index_access(
	env: &Env,
	target_expr: &TokenTree<'_>,
	index_expr: &TokenTree<'_>,
) -> Result<TypedExpr, RuntimeError> {
	let target = infer_expr(env, target_expr)?;
	let index = infer_expr(env, index_expr)?;
	let ty = match &target.ty {
		ty if is_dyn_like(ty) => Type::Dyn,
		Type::List(element) => {
			ensure_index_operand(&index.ty, "list")?;
			(**element).clone()
		}
		Type::String => {
			ensure_index_operand(&index.ty, "string")?;
			Type::String
		}
		Type::Bytes => {
			ensure_index_operand(&index.ty, "bytes")?;
			Type::Uint
		}
		Type::Map(key_ty, value_ty) => {
			if !is_assignable(key_ty, &index.ty, env) {
				return Err(RuntimeError::new(format!(
					"Map index expects type {} but found {}",
					describe_type(key_ty),
					describe_type(&index.ty)
				)));
			}
			(**value_ty).clone()
		}
		Type::Struct(name) => {
			if let Some(field) = static_field_name(index_expr) {
				struct_field_type(env, name, &field)?
			} else {
				Type::Dyn
			}
		}
		Type::Null => {
			return Err(RuntimeError::new("Cannot index null"));
		}
		other => {
			return Err(RuntimeError::new(format!(
				"Index operator is not supported for values of kind {}",
				describe_type(other)
			)));
		}
	};
	Ok(TypedExpr::new(
		ty,
		ExprKind::Index {
			target: Box::new(target),
			index: Box::new(index),
		},
	))
}

fn infer_in_operator(
	env: &Env,
	needle_expr: &TokenTree<'_>,
	haystack_expr: &TokenTree<'_>,
) -> Result<TypedExpr, RuntimeError> {
	let needle = infer_expr(env, needle_expr)?;
	let haystack = infer_expr(env, haystack_expr)?;
	match &haystack.ty {
		Type::List(element) => {
			if !is_assignable(element, &needle.ty, env) && !is_dyn_like(&needle.ty) {
				return Err(RuntimeError::new(format!(
					"Operator 'in' expects element type {} but found {}",
					describe_type(element),
					describe_type(&needle.ty)
				)));
			}
		}
		Type::Map(key_ty, _) => {
			if !is_assignable(key_ty, &needle.ty, env) && !is_dyn_like(&needle.ty) {
				return Err(RuntimeError::new(format!(
					"Operator 'in' expects key type {} but found {}",
					describe_type(key_ty),
					describe_type(&needle.ty)
				)));
			}
		}
		Type::String => {
			if !is_assignable(&Type::String, &needle.ty, env)
				&& !is_dyn_like(&needle.ty)
			{
				return Err(RuntimeError::new(
					"String containment expects a string needle",
				));
			}
		}
		Type::Bytes => {
			if !is_assignable(&Type::Bytes, &needle.ty, env)
				&& !is_dyn_like(&needle.ty)
			{
				return Err(RuntimeError::new(
					"Bytes containment expects a bytes needle",
				));
			}
		}
		ty if is_dyn_like(ty) => {}
		other => {
			return Err(RuntimeError::new(format!(
				"Operator 'in' is not supported for values of kind {}",
				describe_type(other)
			)));
		}
	}
	Ok(make_binary(BinaryOp::In, Type::Bool, needle, haystack))
}

fn infer_call(
	env: &Env,
	func: &TokenTree<'_>,
	args: &[TokenTree<'_>],
	is_method: bool,
) -> Result<TypedExpr, RuntimeError> {
	let name = resolve_function_name(func).ok_or_else(|| {
		RuntimeError::new("function calls must reference an identifier")
	})?;
	let decl = env.lookup_function(&name).ok_or_else(|| {
		RuntimeError::new(format!(
			"Function '{name}' is not declared in the environment"
		))
	})?;
	let typed_args = args
		.iter()
		.map(|expr| infer_expr(env, expr))
		.collect::<Result<Vec<_>, _>>()?;
	let arg_types = typed_args
		.iter()
		.map(|expr| expr.ty.clone())
		.collect::<Vec<_>>();
	if let Some(overload) = select_overload(env, decl, &arg_types, is_method) {
		return Ok(TypedExpr::new(
			overload.result.clone(),
			ExprKind::Call {
				function: name,
				args: typed_args,
				is_method,
			},
		));
	}
	Err(RuntimeError::new(format!(
		"Function '{}' does not have an overload matching arguments ({})",
		name,
		format_type_list(&arg_types)
	)))
}

fn resolve_function_name(expr: &TokenTree<'_>) -> Option<String> {
	match expr {
		TokenTree::Atom(Atom::Ident(name)) => Some((*name).to_string()),
		TokenTree::Cons(Op::Field, nodes) if nodes.len() == 2 => {
			let left = resolve_function_name(&nodes[0])?;
			let right = resolve_function_name(&nodes[1])?;
			Some(format!("{left}.{right}"))
		}
		_ => None,
	}
}

fn select_overload<'a>(
	env: &Env,
	decl: &'a FunctionDecl,
	arg_types: &[Type],
	is_method: bool,
) -> Option<&'a OverloadDecl> {
	decl
		.overloads
		.iter()
		.find(|overload| matches_overload(env, overload, arg_types, is_method))
}

fn matches_overload(
	env: &Env,
	overload: &OverloadDecl,
	arg_types: &[Type],
	is_method: bool,
) -> bool {
	let (method_receiver, method_args) = if is_method {
		if arg_types.is_empty() {
			return false;
		}
		(Some(&arg_types[0]), &arg_types[1..])
	} else {
		(None, arg_types)
	};

	let (receiver, remaining_args): (Option<&Type>, &[Type]) =
		if overload.receiver.is_some() {
			if let Some(receiver_ty) = method_receiver {
				(Some(receiver_ty), method_args)
			} else if !method_args.is_empty() {
				(Some(&method_args[0]), &method_args[1..])
			} else {
				return false;
			}
		} else {
			if method_receiver.is_some() {
				return false;
			}
			(None, method_args)
		};

	if overload.args.len() != remaining_args.len() {
		return false;
	}

	if let (Some(expected), Some(actual)) = (overload.receiver.as_ref(), receiver) {
		if !is_assignable(expected, actual, env) {
			return false;
		}
	} else if overload.receiver.is_some() && receiver.is_none() {
		return false;
	}

	overload
		.args
		.iter()
		.zip(remaining_args.iter())
		.all(|(expected, actual)| is_assignable(expected, actual, env))
}

fn static_field_name(expr: &TokenTree<'_>) -> Option<String> {
	match expr {
		TokenTree::Atom(Atom::Ident(name)) => Some((*name).to_string()),
		TokenTree::Atom(Atom::String(value)) => Some(value.to_string()),
		_ => None,
	}
}

fn struct_field_type(
	env: &Env,
	name: &TypeName,
	field: &str,
) -> Result<Type, RuntimeError> {
	let named = env.lookup_type(name).ok_or_else(|| {
		RuntimeError::new(format!(
			"Unknown struct type '{}' referenced in expression",
			name.as_str()
		))
	})?;
	let NamedType::Struct(strct) = named else {
		return Err(RuntimeError::new(format!(
			"Named type '{}' is not a struct",
			name.as_str()
		)));
	};
	strct
		.fields
		.get(field)
		.map(|field_decl| field_decl.ty.clone())
		.ok_or_else(|| {
			RuntimeError::new(format!(
				"Struct '{}' does not contain field '{}'",
				name.as_str(),
				field
			))
		})
}

fn infer_addition_type(
	env: &Env,
	left: &Type,
	right: &Type,
) -> Result<Type, RuntimeError> {
	if is_dyn_like(left) || is_dyn_like(right) {
		return Ok(Type::Dyn);
	}
	match (left, right) {
		(Type::String, Type::String) => Ok(Type::String),
		(Type::Bytes, Type::Bytes) => Ok(Type::Bytes),
		(Type::List(a), Type::List(b)) => {
			let merged = unify_types(env, (**a).clone(), (**b).clone())?;
			Ok(Type::list(merged))
		}
		_ => numeric_binary_result(left, right, NumericBinaryOp::Add),
	}
}

fn expect_boolean(ty: &Type, context: &str) -> Result<(), RuntimeError> {
	if matches!(ty, Type::Bool) || is_dyn_like(ty) {
		Ok(())
	} else {
		Err(RuntimeError::new(format!(
			"{context} expects a bool but found {}",
			describe_type(ty)
		)))
	}
}

fn ensure_comparable(
	left: &Type,
	right: &Type,
	op: Op,
) -> Result<(), RuntimeError> {
	if is_dyn_like(left) || is_dyn_like(right) {
		return Ok(());
	}
	let comparable = (is_numeric_type(left) && is_numeric_type(right))
		|| matches!(left, Type::String) && matches!(right, Type::String)
		|| matches!(left, Type::Bytes) && matches!(right, Type::Bytes);
	if comparable {
		Ok(())
	} else {
		Err(RuntimeError::new(format!(
			"Operator '{op:?}' is not defined for types {} and {}",
			describe_type(left),
			describe_type(right)
		)))
	}
}

fn ensure_index_operand(
	ty: &Type,
	context: &str,
) -> Result<(), RuntimeError> {
	if matches!(ty, Type::Int | Type::Uint) || is_dyn_like(ty) {
		Ok(())
	} else {
		Err(RuntimeError::new(format!(
			"{context} index expects an integer but found {}",
			describe_type(ty)
		)))
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum NumericKind {
	Int,
	Uint,
	Double,
}

#[derive(Clone, Copy)]
enum NumericBinaryOp {
	Add,
	Subtract,
	Multiply,
	Divide,
	Modulo,
}

impl NumericBinaryOp {
	fn description(self) -> &'static str {
		match self {
			NumericBinaryOp::Add => "addition",
			NumericBinaryOp::Subtract => "subtraction",
			NumericBinaryOp::Multiply => "multiplication",
			NumericBinaryOp::Divide => "division",
			NumericBinaryOp::Modulo => "modulo",
		}
	}
}

fn numeric_kind(ty: &Type, context: &str) -> Result<NumericKind, RuntimeError> {
	match ty {
		Type::Int => Ok(NumericKind::Int),
		Type::Uint => Ok(NumericKind::Uint),
		Type::Double => Ok(NumericKind::Double),
		_ => Err(RuntimeError::new(format!(
			"{context} expects numeric values but found {}",
			describe_type(ty)
		))),
	}
}

fn numeric_unary_result(operand: &Type, context: &str) -> Result<Type, RuntimeError> {
	if is_dyn_like(operand) {
		return Ok(Type::Dyn);
	}
	match operand {
		Type::Int => Ok(Type::Int),
		Type::Double => Ok(Type::Double),
		_ => Err(RuntimeError::new(format!(
			"{context} expects int or double but found {}",
			describe_type(operand)
		))),
	}
}

fn numeric_binary_result(
	left: &Type,
	right: &Type,
	op: NumericBinaryOp,
) -> Result<Type, RuntimeError> {
	if is_dyn_like(left) || is_dyn_like(right) {
		return Ok(Type::Dyn);
	}
	let context = op.description();
	let left_kind = numeric_kind(left, context)?;
	let right_kind = numeric_kind(right, context)?;
	match op {
		NumericBinaryOp::Add | NumericBinaryOp::Subtract | NumericBinaryOp::Multiply => {
			if left_kind == right_kind {
				Ok(type_from_numeric_kind(left_kind))
			} else {
				Ok(Type::Double)
			}
		}
		NumericBinaryOp::Divide => Ok(Type::Double),
		NumericBinaryOp::Modulo => match (left_kind, right_kind) {
			(NumericKind::Int, NumericKind::Int) => Ok(Type::Int),
			(NumericKind::Uint, NumericKind::Uint) => Ok(Type::Uint),
			_ => Err(RuntimeError::new(
				"Modulo operator is only defined for matching integral types",
			)),
		},
	}
}

fn type_from_numeric_kind(kind: NumericKind) -> Type {
	match kind {
		NumericKind::Int => Type::Int,
		NumericKind::Uint => Type::Uint,
		NumericKind::Double => Type::Double,
	}
}

fn is_numeric_type(ty: &Type) -> bool {
	matches!(ty, Type::Int | Type::Uint | Type::Double)
}

fn is_dyn_like(ty: &Type) -> bool {
	matches!(ty, Type::Dyn | Type::Any | Type::TypeParam(_))
}

fn describe_type(ty: &Type) -> String {
	match ty {
		Type::Dyn => "dyn".into(),
		Type::Any => "any".into(),
		Type::Null => "null".into(),
		Type::Type => "type".into(),
		Type::Bool => "bool".into(),
		Type::Int => "int".into(),
		Type::Uint => "uint".into(),
		Type::Double => "double".into(),
		Type::String => "string".into(),
		Type::Bytes => "bytes".into(),
		Type::Timestamp => "timestamp".into(),
		Type::Duration => "duration".into(),
		Type::List(inner) => format!("list<{}>", describe_type(inner)),
		Type::Map(key, value) => {
			format!("map<{}, {}>", describe_type(key), describe_type(value))
		}
		Type::Struct(name) => format!("struct {}", name.as_str()),
		Type::Enum(name) => format!("enum {}", name.as_str()),
		Type::TypeParam(name) => format!("type_param {name}"),
	}
}

fn unify_types(
	env: &Env,
	left: Type,
	right: Type,
) -> Result<Type, RuntimeError> {
	if is_dyn_like(&left) {
		return Ok(right);
	}
	if is_dyn_like(&right) {
		return Ok(left);
	}
	if left == right {
		return Ok(left);
	}
	if let Some(numeric) = merge_numeric_types(&left, &right) {
		return Ok(numeric);
	}
	match (&left, &right) {
		(Type::List(a), Type::List(b)) => {
			let merged = unify_types(env, (**a).clone(), (**b).clone())?;
			Ok(Type::list(merged))
		}
		(Type::Map(ka, va), Type::Map(kb, vb)) => {
			let key = unify_types(env, (**ka).clone(), (**kb).clone())?;
			let value = unify_types(env, (**va).clone(), (**vb).clone())?;
			Ok(Type::map(key, value))
		}
		_ => Err(RuntimeError::new(format!(
			"Type mismatch between {} and {}",
			describe_type(&left),
			describe_type(&right)
		))),
	}
}

fn merge_numeric_types(left: &Type, right: &Type) -> Option<Type> {
	match (left, right) {
		(Type::Int, Type::Int) => Some(Type::Int),
		(Type::Uint, Type::Uint) => Some(Type::Uint),
		(Type::Double, Type::Double) => Some(Type::Double),
		(Type::Int, Type::Double)
		| (Type::Double, Type::Int)
		| (Type::Uint, Type::Double)
		| (Type::Double, Type::Uint)
		| (Type::Uint, Type::Int)
		| (Type::Int, Type::Uint) => Some(Type::Double),
		_ => None,
	}
}

fn is_assignable(expected: &Type, actual: &Type, env: &Env) -> bool {
	if expected == actual {
		return true;
	}
	if is_dyn_like(expected) || is_dyn_like(actual) {
		return true;
	}
	match (expected, actual) {
		(Type::List(a), Type::List(b)) => is_assignable(a, b, env),
		(Type::Map(ka, va), Type::Map(kb, vb)) => {
			is_assignable(ka, kb, env) && is_assignable(va, vb, env)
		}
		(Type::Struct(a), Type::Struct(b)) => a == b,
		(Type::Enum(a), Type::Enum(b)) => a == b,
		_ => false,
	}
}

fn format_type_list(types: &[Type]) -> String {
	types
		.iter()
		.map(|ty| describe_type(ty))
		.collect::<Vec<_>>()
		.join(", ")
}

fn make_binary(
	op: BinaryOp,
	ty: Type,
	left: TypedExpr,
	right: TypedExpr,
) -> TypedExpr {
	TypedExpr::new(
		ty,
		ExprKind::Binary {
			op,
			left: Box::new(left),
			right: Box::new(right),
		},
	)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::env::Env;
	use crate::parser::{Atom, TokenTree};
	use crate::types::{FieldDecl, FunctionDecl, IdentDecl, NamedType, OverloadDecl, StructType};

	fn declared_user_env() -> Env {
		const USER_TYPE: &str = "example.User";
		let mut user = StructType::new(USER_TYPE);
		user.add_field("name", FieldDecl::new(Type::String)).unwrap();
		user.add_field("roles", FieldDecl::new(Type::list(Type::String)))
			.unwrap();

		let mut builder = Env::builder();
		builder.add_type(NamedType::Struct(user.clone())).unwrap();
		builder
			.add_ident(
				IdentDecl::new("user", Type::struct_type(user.name.clone())),
			)
			.unwrap();

		let mut func = FunctionDecl::new("has_role");
		func.add_overload(
			OverloadDecl::new("user_has_role_string", vec![Type::String], Type::Bool)
				.with_receiver(Type::struct_type(user.name.clone())),
		)
		.unwrap();
		builder.add_function(func).unwrap();
		builder.build()
	}

	#[test]
	fn infers_identifier_types() {
		let mut builder = Env::builder();
		builder.add_ident(IdentDecl::new("x", Type::Int)).unwrap();
		let env = builder.build();
		let expr = type_check(&env, &TokenTree::Atom(Atom::Ident("x"))).unwrap();
		assert_eq!(expr.ty, Type::Int);
	}

	#[test]
	fn infers_method_call_type() {
		let env = declared_user_env();
		let mut parser = crate::parser::Parser::new("user.has_role('admin')");
		let tree = parser.parse().expect("parse");
		let typed = type_check(&env, &tree).expect("type check");
		assert_eq!(typed.ty, Type::Bool);
	}

	#[test]
	fn reports_unknown_identifier() {
		let env = Env::builder().build();
		let mut parser = crate::parser::Parser::new("missing + 1");
		let tree = parser.parse().expect("parse");
		let err = type_check(&env, &tree).expect_err("type error");
		assert!(err.to_string().contains("Identifier 'missing'"));
	}
}
