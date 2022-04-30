#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var(String);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunName(String);

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
#[repr(u64)]
pub enum PrimOp2 {
    AddOp, MulOp
}

#[derive(Debug, Clone, PartialEq)]
#[repr(u64)]
pub enum Expr {
    LitExpr(u64),
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

#[derive(Debug, Clone, PartialEq)]
#[repr(u64)]
pub enum Error {
    UnboundVar(Var),
    UnknownFun(FunName),
    Unimplemented,
    WrongNumberOfArgs,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDef {
    fun_args : Vec<Var>,
    fun_body : Stmt,
}

#[derive(Clone, Debug)]
pub struct Env {
    var_map : Vec<(Var, u64)>,
    fun_map : Vec<(FunName, FunDef)>,
}

pub fn fresh_env_from_env <'a> (e : &'a Env) -> Env {
    Env { var_map : Vec::new (),
          fun_map : e.fun_map.clone () }
}

pub fn ref_ref_eq <'a, 'b, 'c, T: Eq> (v1 : &'a T, v2 : &'b&'c T) -> bool {
    v1 == *v2
}

pub fn env_lookup <'a, 'b> (env : &'a Env, x : &'b Var) -> Result <u64, Error> {
    match env.var_map.iter().rev().find(|y| ref_ref_eq(x, &&y.0)) {
        Some(v) => Ok(v.1),
        None => Err(Error::UnboundVar (x.clone ()))
    }
}

pub fn env_update <'a,'b> (env : &'a mut Env, x : &'b Var, v : u64) {
    env.var_map.push ( (x.clone(), v) );
}

pub fn fun_lookup <'a,'b> (env : &'a Env, f : &'b FunName) -> Result<&'a FunDef,Error> {
    match env.fun_map.iter().rev().find(|g| ref_ref_eq(f, &&g.0)) {
        Some (d) => Ok(&d.1),
        None => Err(Error::UnknownFun (f.clone ()))
    }
}

pub fn eval_primop2 <'a> (f : &'a PrimOp2, v1: u64, v2: u64) -> u64 {
    match f {
        PrimOp2::AddOp => v1 + v2,
        PrimOp2::MulOp => v1 * v2,
    }
}

pub fn eval_expr <'a, 'b> (env : &'a Env, e : &'b Expr) -> Result<u64,Error> {
    match e {
        Expr::LitExpr (l) => Ok(*l),
        Expr::VarExpr (x) => env_lookup (env, x),
        Expr::Apply2Expr (f, arg1, arg2) =>
            { let v1 = eval_expr (env, arg1)?;
              let v2 = eval_expr (env, arg2)?;
              Ok(eval_primop2 (f, v1, v2)) }
    }
}

pub fn eval_stmt <'a, 'b> (env : &'a mut Env, stmt : &'b Stmt) -> Result<u64, Error> {
    match stmt {
        Stmt::Return (x) => env_lookup (env, x),
        Stmt::Skip => Ok (0),
        Stmt::Assign (x,e) =>
        { let v = eval_expr (env, e) ?;
          env_update (env, x, v);
          Ok (0)
        }
        Stmt::IfStmt (e, stmt1, stmt2) =>
        { let v = eval_expr (env, e) ?;
          if v != 0 { eval_stmt (env, stmt1) } else { eval_stmt (env, stmt2) }
        },
        Stmt::WhileStmt (e, body) =>
        { let v = eval_expr (env, e) ?;
          if v != 0 { let _ = eval_stmt (env, body) ?;
                      eval_stmt (env, stmt) }
          else { Ok(0) } }
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


pub fn eval_stmt_alt <'a, 'b> (env : &'a mut Env, stmt : &'b Stmt) -> Result<u64, Error> {
    match stmt {
        Stmt::Return (x) => env_lookup (env, x),
        Stmt::Skip => Ok (0),
        Stmt::Assign (x,e) =>
        { match eval_expr (env, e) {
            Ok (v) => { env_update (env, x, v); Ok (0) },
            Err (e) => Err (e),
        }}
        Stmt::IfStmt (e, stmt1, stmt2) =>
        { match eval_expr (env, e) {
            Ok (v) => {
                if v != 0 { eval_stmt_alt (env, stmt1) }
                else { eval_stmt_alt (env, stmt2) }
            },
            Err (e) => Err (e),
        }},
        Stmt::WhileStmt (e, body) =>
        { match eval_expr (env, e) {
            Ok (v) => {
                if v != 0 {
                    match eval_stmt_alt (env, body) {
                        Ok (_) => eval_stmt_alt (env, stmt),
                        Err (e) => Err (e) }
                }
                else { Ok(0) } },
            Err (e) => Err (e),
        }}
        Stmt::CallStmt (_, _) => Err (Error::Unimplemented)
        /*
        Stmt::CallStmt (f, args) =>
        { match fun_lookup (env, f) {
            Ok (f_def) => {
                let mut new_env = fresh_env_from_env (env);
                if args.len () == f_def.fun_args.len () {
                    for (x, arg) in f_def.fun_args.iter().zip(args.iter()) {
                        match eval_expr (env, arg) {
                            Ok (v) => env_update (&mut new_env, x, v),
                            Err (e) => Err (e)
                        }
                    };
                    eval_stmt (&mut new_env, &(*f_def).fun_body)
                } else { Err (Error::WrongNumberOfArgs)}},
            Err (e) => Err (e)
        }} */
    }
}
