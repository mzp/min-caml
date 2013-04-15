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

let rec range a b =
  if a >= b then
    []
  else
    a :: range (a+1) b

let tee x f =
  f x;
  x

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
    module_ : Llvm.llmodule;
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

  let any_pointer_type { llcontext; _ } =
    pointer_type (i8_type llcontext)

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
          let f =
            args
            +> List.map (of_type t)
            +> (fun xs -> (any_pointer_type t) :: xs)
            +> Array.of_list
            +> function_type (of_type t ret)
            +> pointer_type
          in
          struct_type llcontext [| f; any_pointer_type t |]
      | Tuple ts ->
          struct_type llcontext (array_map (of_type t) ts)
      | Array _ ->
          assert false
      | Var _ ->
          assert false

  let func_type ({ llcontext } as t) =
    let open Type in
    function
     | Fun (args, ret) ->
         (* top level function becomes function.
          * otherwise becomes function *pointer* *)
         args
         +> List.map (of_type t)
         +> (fun xs -> (any_pointer_type t) :: xs)
         +> Array.of_list
         +> function_type (of_type t ret)
     | _ ->
         failwith "expect function type"

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
    declare_function name ty t.module_

  let define_fun ({ llcontext; builder; module_ } as t) name ty ~f =
    let fun_ =
      declare_fun t name ty
    in
    let () =
      ignore @@ block t "entry" fun_ ~f:(fun () ->
        let params =
          Array.to_list @@ Llvm.params fun_
        in
        ignore @@ build_ret (f t fun_ params) builder)
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

  let null { llcontext; _} =
    const_pointer_null (pointer_type (i8_type llcontext))

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

  let gep { builder; _ } x n =
    build_struct_gep x n (Id.gentmp Type.Int) builder

  let struct_alloc ({ builder; llcontext; _ } as t) xs =
    let p =
      build_alloca (struct_type llcontext @@ Array.map type_of xs) "p" builder
    in
    let () =
      ArrayLabels.iteri xs ~f:begin fun i x ->
        ignore @@ build_store x (gep t p i) builder
      end
    in
    p

  let struct_ ({ builder; _ } as t) xs =
    let p =
      struct_alloc t xs
    in
    build_load p "p" builder

  let struct_ref { builder; _ } x n =
    build_extractvalue x n (Id.gentmp Type.Int) builder

  let struct_data ({ builder; _ } as t) xs =
    let p =
      struct_alloc t xs
    in
    build_pointercast p (any_pointer_type t) "p" builder

  let struct_load ({builder; llcontext; _ } as t) ty p =
    if ty = [] then
      []
    else
      let pty =
        pointer_type @@
          struct_type llcontext @@
          array_map (of_type t) @@
          List.map snd ty
      in
      let s =
        build_pointercast p pty "p" builder
      in
      ListLabels.mapi ty ~f:begin fun n (name, _) ->
        build_load (gep t s n) name builder
      end

  let init_array ({ builder; llcontext; _} as t) xs n v =
  (*
       %p = alloca i32
       store i32 0, i32* %p
       br label %init.cond

     init.cond:
       %i = load i32* %p
       %cond= icmp slt i32 %i, 10
       br i1 %cond, %init.body, %init.end

     init.body:
       %i = load i32* %p
       %gep = getelementptr inbounds i32* %xs, i32 %i
       store i32 v, i32* %gep
       %i = add i32 %i, 1
       store i32 %i, i32* %p
       br %init.cond

     init.end:
  *)
    let start_bb =
      current_block t
    in
    let fun_ =
      block_parent start_bb
    in
    let p =
      build_alloca (i32_type llcontext) "p" builder
    in
    let _ =
      build_store (int t 0) p builder
    in
    (* (1) *)
    let (cond_bb, ())   =
      block t "init.cond" fun_ ~f:begin fun () ->
        ()
      end
    in
    (* (2) *)
    let (body_bb, ())  =
      block t "init.body" fun_ ~f:begin fun () ->
        let i =
          build_load p "i" builder
        in
        let _ =
          build_store v (build_in_bounds_gep xs [| i |] "gep" builder) builder
        in
        let _ =
          build_store (add t i (int t 1)) p builder
        in
        ignore @@ br t cond_bb
     end
    in
    let (end_bb, ())  =
      block t "init.end" fun_ ~f:begin fun () ->
        ()
     end
    in
    (* (4) *)
    let ()  =
      update_block t cond_bb ~f:begin fun () ->
        let i =
          build_load p "i" builder
        in
        let cond =
          icmp t Icmp.Slt i n
        in
        ignore @@ cond_br t cond body_bb end_bb
      end
    in
    let ()  =
      update_block t start_bb ~f:begin fun () ->
        ignore @@ br t cond_bb
      end
    in
    let ()  =
      update_block t end_bb ~f:begin fun () ->
        ()
      end
    in
    ()

  let create_array ({ builder; _ } as t) n value =
    let xs =
      build_array_alloca (type_of value) n "array" builder
    in
    init_array t xs n value;
    xs

  let array_ref { builder; _ } xs n =
    build_load (build_in_bounds_gep xs [| n |] "gep" builder) "array_element" builder

  let array_set ({ builder; _ } as t) xs n v =
    ignore @@ build_store v (build_in_bounds_gep xs [| n |] "gep" builder) builder;
    unit t

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
    | MakeCls ((name, ty), { entry; Closure.actual_fv }, body) ->
        let fv =
          IR.struct_data ir (array_map (flip Env.varref env) actual_fv)
        in
        let cls =
          IR.struct_ ir [|
            Env.varref (string_of_id entry) env;
            fv
        |]
        in
        let env =
          Env.def name ty cls env
        in
        f (ir, env) body
    | AppCls (name, args) ->
        let f  =
          IR.struct_ref ir (Env.varref name env) 0
        in
        let fv =
          IR.struct_ref ir (Env.varref name env) 1
        in
        let args =
          List.map (flip Env.varref env) args
        in
        IR.fun_call ir f @@ Array.of_list ( fv :: args )
    | AppDir (Id.L "min_caml_create_array", [n; value]) ->
        IR.create_array ir (Env.varref n env) (Env.varref value env)
    | AppDir (f, args) ->
        let f =
          Env.varref (string_of_id f) env
        in
        let args =
          List.map (flip Env.varref env) args
        in
        IR.fun_call ir f @@ Array.of_list (IR.null ir :: args)
    | Tuple xs ->
        IR.struct_ ir (array_map (flip Env.varref env) xs)
    | Get (xs, n) ->
        IR.array_ref ir (Env.varref xs env) (Env.varref n env)
    | Put (xs, n, v) ->
        IR.array_set ir
           (Env.varref xs env)
           (Env.varref n  env)
           (Env.varref v  env)
    | ExtArray _ -> assert false
end

module GenFunction = struct
  let import_extfun (ir, env) =
    let f name ty env =
      let name =
        "min_caml_" ^ name
      in
      let v =
        IR.declare_fun ir name (IR.func_type ir ty)
      in
      Env.def name ty v env
    in
    M.fold f !Typing.extenv env

  let add_env args params env =
    params
    +> List.combine args
    +> ListLabels.fold_left ~init:env ~f:begin fun env ((x, ty), v) ->
      Env.def x ty v env
    end

 let generate_closure (ir, env) { Closure.name = (name, ty); args; formal_fv; body } =
    ty, IR.define_fun ir (string_of_id name) (IR.func_type ir ty) ~f:begin fun
      ir fun_ params ->
      (* argument *)
      let env =
        add_env args (List.tl @@ params) env
      in
      (* fv *)
      let actual_fv =
        IR.struct_load ir formal_fv @@ List.hd params
      in
      let env =
        add_env formal_fv actual_fv env
      in
      (* self *)
      let env =
        Env.def (string_of_id name) ty fun_ env
      in
      GenValue.f (ir, env) body
    end

  let f (ir, env) ( { Closure.formal_fv; name=(name,_) } as closure) =
    let ty, fun_ =
      generate_closure (ir, env) closure
    in
    (ir, Env.def (string_of_id name) ty fun_ env)
end

module GenMain = struct
  let f (ir,env) body =
    let ty =
      function_type (IR.of_type ir Type.Unit)
        [| IR.any_pointer_type ir; IR.any_pointer_type ir|]
    in
    ignore @@ IR.define_fun ir "min_caml_start" ty  ~f:begin fun ir _ _ ->
      GenValue.f (ir, env) body
    end
end

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
  let () =
    GenMain.f (ir, env) body
  in
  let module_ =
    IR.module_ ir
  in
  Llvm_analysis.assert_valid_module module_;
  module_
