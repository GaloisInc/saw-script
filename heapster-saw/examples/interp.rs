#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var(String);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunName(String);

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
#[repr(u64)]
pub enum PrimOp2 {
    AddOp, MulOp
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Lit {
    BoolLit (bool),
    IntLit (u64),
}

#[derive(Debug, Clone, PartialEq)]
#[repr(u64)]
pub enum Expr {
    LitExpr(Lit),
    VarExpr(Var),
    Apply2Expr(PrimOp2, Box<Expr>, Box<Expr>)
}

#[derive(Debug, Clone, PartialEq)]
#[repr(u64)]
pub enum Stmt {
    Return(Var),
    Skip,
    Assign(Var,Expr),
    IfStmt(Expr,Box<Stmt>,Box<Stmt>),
    WhileStmt(Expr,Box<Stmt>),
    CallStmt(FunName, Vec<Expr>)
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum Value {
    BoolValue (bool),
    IntValue (u64)
}

#[derive(Debug, Clone, PartialEq)]
#[repr(u64)]
pub enum Error {
    UnboundVar(Var),
    UnknownFun(FunName),
    Unimplemented,
    IncorrectType,
    WrongNumberOfArgs,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDef {
    fun_args : Vec<Var>,
    fun_body : Stmt,
}

#[derive(Clone, Debug)]
pub struct Env {
    var_map : Vec<(Var, Value)>,
    fun_map : Vec<(FunName, FunDef)>,
}

pub fn fresh_env_from_env <'a> (e : &'a Env) -> Env {
    Env { var_map : Vec::new (),
          fun_map : e.fun_map.clone () }
}

pub fn value_bool (v:Value) -> Result<bool,Error> {
    match v {
        Value::BoolValue (b) => Ok (b),
        Value::IntValue (_) => Err (Error::IncorrectType),
    }
}

pub fn value_u64 (v:Value) -> Result<u64,Error> {
    match v {
        Value::BoolValue (_) => Err (Error::IncorrectType),
        Value::IntValue (i) => Ok (i)
    }
}

pub fn lit_value <'a> (l:&'a Lit) -> Value {
    match l {
        Lit::BoolLit (b) => Value::BoolValue (*b),
        Lit::IntLit (i) => Value::IntValue (*i),
    }
}

pub fn ref_ref_eq <'a, 'b, 'c, T: Eq> (v1 : &'a T, v2 : &'b&'c T) -> bool {
    v1 == *v2
}

pub fn env_lookup <'a, 'b> (env : &'a Env, x : &'b Var) -> Result <Value, Error> {
    match env.var_map.iter().rev().find(|y| ref_ref_eq(x, &&y.0)) {
        Some(v) => Ok(v.1),
        None => Err(Error::UnboundVar (x.clone ()))
    }
}

pub fn env_update <'a,'b> (env : &'a mut Env, x : &'b Var, v : Value) {
    env.var_map.push ( (x.clone(), v) );
}

pub fn fun_lookup <'a,'b> (env : &'a Env, f : &'b FunName) -> Result<&'a FunDef,Error> {
    match env.fun_map.iter().rev().find(|g| ref_ref_eq(f, &&g.0)) {
        Some (d) => Ok(&d.1),
        None => Err(Error::UnknownFun (f.clone ()))
    }
}

pub fn eval_primop2 (f : PrimOp2, v1: Value, v2:Value) -> Result<Value,Error> {
    match f {
        PrimOp2::AddOp => { let i1 = value_u64 (v1)?;
                            let i2 = value_u64 (v2)?;
                            Ok (Value::IntValue (i1 + i2)) },
        PrimOp2::MulOp => { let i1 = value_u64 (v1)?;
                            let i2 = value_u64 (v2)?;
                            Ok (Value::IntValue (i1 + i2)) },
    }
}

pub fn eval_expr <'a, 'b> (env : &'a Env, e : &'b Expr) -> Result<Value,Error> {
    match e {
        Expr::LitExpr (l) => Ok (lit_value (l)),
        Expr::VarExpr (x) => env_lookup (env, x),
        Expr::Apply2Expr (f, arg1, arg2) =>
            { let v1 = eval_expr (env, arg1)?;
              let v2 = eval_expr (env, arg2)?;
              eval_primop2 (*f, v1, v2) }
    }
}

pub fn eval_stmt <'a, 'b> (env : &'a mut Env, stmt : &'b Stmt) -> Result<Value,Error> {
    match stmt {
        Stmt::Return (x) => env_lookup (env, x),
        Stmt::Skip => Ok (Value::IntValue (0)),
        Stmt::Assign (x,e) =>
        { let v = eval_expr (env, e) ?;
          env_update (env, x, v);
          Ok (Value::IntValue (0))
        }
        Stmt::IfStmt (e, stmt1, stmt2) =>
        { let v = eval_expr (env, e) ?;
          let b = value_bool (v) ?;
          if b { eval_stmt (env, stmt1) } else { eval_stmt (env, stmt2) }
        },
        Stmt::WhileStmt (e, body) =>
        { let v = eval_expr (env, e) ?;
          let b = value_bool (v) ?;
          if b { let _ = eval_stmt (env, body) ?;
                 eval_stmt (env, stmt) }
          else { Ok (Value::IntValue (0)) }}
        Stmt::CallStmt (f, args) =>
        { let f_def = fun_lookup (env, f) ?;
          let mut new_env = fresh_env_from_env (env);
          if args.len () == f_def.fun_args.len () {
              for (x, arg) in f_def.fun_args.iter().zip(args.iter()) {
                  let v = eval_expr (env, arg) ?;
                  env_update (&mut new_env, x, v)
              };
              eval_stmt (&mut new_env, &(*f_def).fun_body)
          } else { Err (Error::WrongNumberOfArgs)}
        }
    }
}
