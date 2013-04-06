open Llvm

(* utils *)
let (@@) f x =
  f x

let (+>) x f =
  f x

let ($) f g x =
  f (g x)

let uncurry f (x, y) =
  f x y

let flip f x y =
  f y x

let is_prefix prefix str =
  String.sub str 0 (String.length prefix) = prefix

let array_map f xs =
  Array.of_list @@ List.map f xs

let string_of_id (Id.L str) =
  str



(* env *)
module Env = struct
  type t = {
    venv : Llvm.llvalue M.t;
    tenv : Type.t M.t
  }

  let empty = {
    venv = M.empty;
    tenv = M.empty
  }

  let def name ty v { venv; tenv } = 
    set_value_name name v;
    {
      venv = M.add name v  venv;
      tenv = M.add name ty tenv
    }

  let varref name { venv; _ } =
    M.find name venv

  let tyref name { tenv; _ } =
    M.find name tenv
end

module IR = struct
  open Llvm
  type t = {
    llcontext : Llvm.llcontext;
    builder : Llvm.llbuilder;
    module_ : Llvm.llmodule
  }

  let module_ { module_; _ } =
    module_

  let init () = 
    let llcontext =
      Llvm.global_context ()
    in
    let builder =
      Llvm.builder llcontext
    in
    let module_ = 
      create_module llcontext "mincaml_module"
    in
    { llcontext; builder; module_ }
 

  let rec of_type ({ llcontext } as t) =
    let open Type in
    function
      | Unit | Bool ->
          i1_type llcontext
      | Int ->
          i32_type llcontext
      | Float ->
          double_type llcontext
      | Fun (args, ret) ->
          args
          +> array_map (of_type t)
          +> function_type (of_type t ret)
      | Tuple _ ->
          assert false
      | Array _ ->
          assert false
      | Var _ ->
          assert false

  let declare_fun t name ty =
    declare_function name (of_type t ty) t.module_

  let define_fun ({ llcontext; builder; module_ } as t) name ty ~f =
    let fun_ =
      declare_fun t name ty
    in
    let bb =
      append_block llcontext "entry" fun_
    in
    let () =
      position_at_end bb builder
    in
    let v =
      f fun_ t
    in
    let () = 
      ignore (build_ret v builder)
    in
    dump_value fun_;
    Llvm_analysis.assert_valid_function fun_;
    fun_

  (* call function and retrun value by using temp variable *)
  let fun_call { builder; _} f args =
    let tmp =
      Id.gentmp Type.Int
    in
    build_call f args tmp builder

  let unit t =
    const_int (of_type t Type.Unit) 0

  let int t n =
    const_int (of_type t Type.Int) n

  let float t f =
    const_float (of_type t Type.Float) f
end

module GenValue = struct
  open Closure
  type t = Llvm.llvalue

  let rec f (ir, env) : Closure.t -> Llvm.llvalue =
  function
    | Unit ->
        IR.unit ir
    | Int n ->
        IR.int ir n
    | Float f ->
        IR.float ir f
    | Neg x ->
        const_neg (Env.varref x env) 
    | Add (x, y) ->
        const_add (Env.varref x env) (Env.varref y env)
    | Sub (x, y) ->
        const_sub (Env.varref x env) (Env.varref y env)
    | FNeg x ->
        const_fneg (Env.varref x env)
    | FAdd (x, y) ->
        const_fadd (Env.varref x env) (Env.varref y env)
    | FSub (x, y) ->
        const_fsub (Env.varref x env) (Env.varref y env)
    | FMul (x, y) ->
        const_fmul (Env.varref x env) (Env.varref y env)
    | FDiv (x, y) ->
        const_fdiv (Env.varref x env) (Env.varref y env)
    | IfEq (lhs, rhs, then_, else_) -> 
        assert false
    | IfLE _ -> assert false
    | Let ((x, ty), t1, t2) ->
        let v =
          f (ir, env) t1
        in
        f (ir, Env.def x ty v env) t2
    | Var name ->
        Env.varref name env
    | MakeCls _ -> assert false
    | AppCls _ -> assert false
    | AppDir (f, args) ->
        let f =
          Env.varref (string_of_id f) env 
        in
        let args =
          array_map (flip Env.varref env) args
        in
        IR.fun_call ir f args
    | Tuple _ -> assert false
    | LetTuple _ -> assert false
    | Get _ -> assert false
    | Put _ -> assert false
    | ExtArray _ -> assert false
end

module GenFunction = struct
  let import_extfun (ir, env) =
    let f name ty env =
      let name = 
        "min_caml_" ^ name
      in
      let v = 
        IR.declare_fun ir name ty
      in 
      Env.def name ty v env
    in
    M.fold f !Typing.extenv env 

  let f (ir, env) { Closure.name = (name, ty); args; formal_fv; body } =
    let ty =
      match ty with
      | Type.Fun (_, r) ->
          (* add formal_fv's type to signature *)
          Type.Fun (List.map snd (args @ formal_fv), r) 
      | _ ->
          failwith "must not happen"
    in
    let fun_ =
      IR.define_fun ir (string_of_id name) ty ~f:begin fun fun_ ir ->
        (* argument *) 
        let env =
          Array.to_list (params fun_) 
          +> List.combine (args @ formal_fv)
          +> ListLabels.fold_left ~init:env ~f:begin fun env ((x, ty), v) ->
            Env.def x ty v env 
          end
        in
        (* self *)
        let env =
          Env.def (string_of_id name) ty fun_ env
        in
        GenValue.f (ir, env) body
      end
    in
    (ir, Env.def (string_of_id name) ty fun_ env)
end

let stub body = {
  Closure.name = (Id.L "min_caml_start", Type.Fun([], Type.Unit));
  args         = []; 
  formal_fv    = []; 
  body
} 
 
let f (Closure.Prog(funs, body)) =
 let ir =
    IR.init ()
  in
  let env = 
    Env.empty
  in
  let env =
    GenFunction.import_extfun (ir,env)
  in
  let (ir, env) =
    List.fold_left GenFunction.f (ir, env) funs
  in
  let (ir,env) =
    GenFunction.f (ir,env ) (stub body)
  in
  IR.module_ ir
