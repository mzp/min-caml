open Llvm

(* utils *)
let id x =
  x

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

  let typeref name { tenv; _ } =
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
      | Tuple ts ->
          struct_type llcontext (array_map (of_type t) ts)
      | Array _ ->
          assert false
      | Var _ ->
          assert false

  let block { llcontext; builder; _ } name fun_ ~f =
    let bb = 
      append_block llcontext name fun_ 
    in
    let () =
      position_at_end bb builder
    in
    (bb, f ())

  let current_block { builder; _ } = 
    insertion_block builder

  let update_block { builder; _ } bb ~f =
    position_at_end bb builder;
    f ()
    
  let declare_fun t name ty =
    declare_function name (of_type t ty) t.module_

  let define_fun ({ llcontext; builder; module_ } as t) name ty ~f =
    let fun_ =
      declare_fun t name ty
    in
    let () =
      ignore @@ block t "entry" fun_ ~f:(fun () ->
        ignore @@ build_ret (f t fun_) builder)
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

  let phi { builder; _ } xs =
    let tmp =
      Id.gentmp Type.Int
    in
    build_phi xs tmp builder

  let cond_br { builder; _ } cond then_ else_ =
    build_cond_br cond then_ else_ builder

  let br { builder; _ } bb =
    build_br bb builder

  let unit t =
    const_int (of_type t Type.Unit) 0

  let int t n =
    const_int (of_type t Type.Int) n

  let float t f =
    const_float (of_type t Type.Float) f

  let struct_ { llcontext; _ } ts =
    const_struct llcontext ts

  let struct_ref { builder; _ } x n =
     build_extractvalue x n (Id.gentmp Type.Int) builder

  let add { builder; _} x y =
    build_add x y (Id.gentmp Type.Int) builder

  let sub { builder; _} x y =
    build_sub x y (Id.gentmp Type.Int) builder

  let neg { builder; _ } x =
    build_neg x (Id.gentmp Type.Int) builder

  let fadd { builder; _} x y =
    build_fadd x y (Id.gentmp Type.Float) builder

  let fsub { builder; _} x y =
    build_fsub x y (Id.gentmp Type.Float) builder

  let fmul { builder; _} x y =
    build_fmul x y (Id.gentmp Type.Float) builder

  let fdiv { builder; _} x y =
    build_fdiv x y (Id.gentmp Type.Float) builder

  let fneg { builder; _ } x =
    build_fneg x (Id.gentmp Type.Float) builder

  let icmp { builder; _ } op x y =
    build_icmp op x y (Id.gentmp Type.Int) builder

  let fcmp { builder; _ } op x y =
    build_fcmp op x y (Id.gentmp Type.Float) builder

end

module GenValue = struct
  open Closure
  type t = Llvm.llvalue

  let if_ (ir, env) cond then_ else_ =
    (*
        start:
          br <cond>, label %then, label %else ;; (4)

        then:
          %tmp1 = <then>    ;; (1)
          br label %ifcont  ;; (5)

        else:
          %tmp2 = <else>    ;; (2)
          br label %ifcont  ;; (6)

        ifcont:
          %tmp = phi [ %tmp1 %then], [%tmp2, %else ] ;; (3)
    *)

    let start_bb = 
      IR.current_block ir
    in
    let fun_ =
      block_parent start_bb
    in

    (* (1) *)
    let (then_bb, (then_val, then_br))  =
      IR.block ir "then" fun_ ~f:begin fun () ->
        let v =
          then_ (ir, env)
        in
        (v, IR.current_block ir)
      end
    in
    (* (2) *)
    let (else_bb, (else_val, else_br))  =
      IR.block ir "else" fun_ ~f:begin fun () ->
        let v =
          else_ (ir, env)
        in
        (v, IR.current_block ir)
      end
    in
    (* (3) *)
    let (ifcont_bb, phi) =
      IR.block ir "ifcont" fun_ ~f:begin fun () ->
        IR.phi ir  [(then_val, then_br); (else_val, else_br)]
      end
    in
    (* (4) *)
    let ()  =
      IR.update_block ir start_bb ~f:begin fun () ->
        ignore @@ IR.cond_br ir cond then_bb else_bb
      end
    in
    (* (5) *)
    let () =
      IR.update_block ir then_br ~f:(fun () -> ignore @@ IR.br ir ifcont_bb)
    in
    (* (6) *)
    let () =
      IR.update_block ir else_br ~f:(fun () -> ignore @@ IR.br ir ifcont_bb)
    in
    IR.update_block ir ifcont_bb ~f:id;
    phi

  let rec f (ir, env) : Closure.t -> Llvm.llvalue =
  function
    | Unit ->
        IR.unit ir
    | Int n ->
        IR.int ir n
    | Float f ->
        IR.float ir f
    | Neg x ->
        IR.neg ir (Env.varref x env) 
    | Add (x, y) ->
        IR.add ir (Env.varref x env) (Env.varref y env)
    | Sub (x, y) ->
        IR.sub ir (Env.varref x env) (Env.varref y env)
    | FNeg x ->
        IR.fneg ir (Env.varref x env)
    | FAdd (x, y) ->
        IR.fadd ir (Env.varref x env) (Env.varref y env)
    | FSub (x, y) ->
        IR.fsub ir (Env.varref x env) (Env.varref y env)
    | FMul (x, y) ->
        IR.fmul ir (Env.varref x env) (Env.varref y env)
    | FDiv (x, y) ->
        IR.fdiv ir (Env.varref x env) (Env.varref y env)
    | IfEq (x, y, then_, else_) -> 
        let cond =
          match Env.typeref x env, Env.typeref y env with
        | Type.Bool, Type.Bool | Type.Int,Type.Int -> 
            IR.icmp ir Icmp.Eq (Env.varref x env) (Env.varref y env)
        | Type.Float, Type.Float -> 
            IR.fcmp ir Fcmp.Oeq (Env.varref x env) (Env.varref y env)
        | _ -> failwith "equality supported only for bool, int, and float"
        in
        if_ (ir, env) cond (flip f then_) (flip f else_)
    | IfLE (x, y, then_, else_) ->
        let cond =
          match Env.typeref x env, Env.typeref y env with
        | Type.Bool, Type.Bool | Type.Int,Type.Int -> 
            IR.icmp ir Icmp.Sle (Env.varref x env) (Env.varref y env)
        | Type.Float, Type.Float -> 
            IR.fcmp ir Fcmp.Ole (Env.varref x env) (Env.varref y env)
        | _ -> failwith "equality supported only for bool, int, and float"
        in
        if_ (ir, env) cond (flip f then_) (flip f else_)
    | Let ((x, ty), t, body) ->
        let v =
          f (ir, env) t
        in
        f (ir, Env.def x ty v env) body
    | LetTuple (xs, tuple, body) ->
        let tuple =
          Env.varref tuple env
        in
        let i =
          ref 0
        in
        let env =
          ListLabels.fold_left ~init:env xs ~f:begin fun env (x, ty) ->
            let env =
              Env.def x ty (IR.struct_ref ir tuple !i) env
            in
            incr i;
            env
          end
        in
        f (ir, env) body
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
    | Tuple xs ->
        IR.struct_ ir (array_map (flip Env.varref env) xs)
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
      IR.define_fun ir (string_of_id name) ty ~f:begin fun ir fun_ ->
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
