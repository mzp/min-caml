open Llvm

(* utils *)
let (@@) f x =
  f x

let ($) f g x =
  f (g x)

let uncurry f (x, y) =
  f x y

let flip f x y =
  f y x

(* types *)
type context = {
  llcontext : Llvm.llcontext;
  builder : Llvm.llbuilder;
  module_ : Llvm.llmodule;
  table   : (Id.t , Llvm.llvalue) Hashtbl.t;
}

(* code generation *)
let rec of_type ({ llcontext } as context) =
  let open Type in
  function
    | Unit | Bool ->
        i1_type llcontext
    | Int ->
        i32_type llcontext
    | Float ->
        double_type llcontext
    | Fun (targs, t) ->
       function_type (of_type context t) @@ Array.of_list @@ List.map (of_type context) targs
    | Tuple _ ->
        assert false
    | Array _ ->
        assert false
    | Var _ ->
        assert false

let vardef { table } name value =
  Printf.printf "def: %s\n" name;
  Hashtbl.add table name value;
  set_value_name name value

let varref { table } name =
  Printf.printf "ref: %s\n" name;
  Hashtbl.find table name

let string_of_id (Id.L str) =
  str

let declare_fun context name args ret =
  let args_t =
    Array.of_list @@ List.map (of_type context) args
  in
  let ret_t =
    of_type context ret
  in
  let fun_t =
    function_type ret_t args_t
  in
  let value =
    declare_function name fun_t context.module_
  in
  vardef context name value;
  value

let is_prefix prefix str =
  String.sub str 0 (String.length prefix) = prefix

let rec generate_value context : Closure.t -> Llvm.llvalue =
  let open Closure in
  function
    | Unit ->
        const_int (of_type context Type.Unit) 0
    | Int n ->
        const_int (of_type context Type.Int) n
    | Float f ->
        const_float (of_type context Type.Float) f
    | Neg name  ->
        const_neg (varref context name)
    | Add (lhs, rhs) ->
        const_add (varref context lhs) (varref context rhs)
    | Sub (lhs, rhs) ->
        const_sub (varref context lhs) (varref context rhs)
    | FNeg name ->
        const_fneg (varref context name)
    | FAdd (lhs, rhs) ->
        const_fadd (varref context lhs) (varref context rhs)
    | FSub (lhs, rhs) ->
        const_fsub (varref context lhs) (varref context rhs)
    | FMul (lhs, rhs) ->
        const_fmul (varref context lhs) (varref context rhs)
    | FDiv (lhs, rhs) ->
        const_fdiv (varref context lhs) (varref context rhs)
    | IfEq _ -> assert false
    | IfLE _ -> assert false
    | Let ((name, _), t1, t2) ->
        vardef context name @@ generate_value context t1;
        generate_value context t2
    | Var name ->
        varref context name
    | MakeCls _ -> assert false
    | AppCls _ -> assert false
    | AppDir (f, args) ->
       let t =
          Id.gentmp Type.Int in
        let args =
          Array.of_list @@ List.map (varref context) args
        in
        build_call (varref context (string_of_id f)) args t context.builder
    | Tuple _ -> assert false
    | LetTuple _ -> assert false
    | Get _ -> assert false
    | Put _ -> assert false
    | ExtArray _ -> assert false

let ret_type = function
  | Type.Fun (_, t) -> t
  | _ -> assert false

let generate_function ({ llcontext; builder; module_ } as context) { Closure.name = (name, t); args; formal_fv; body } =
  let _ =
    print_endline (string_of_id name) in
  let args =
    args @ formal_fv
  in
  let fun_ =
    declare_fun context (string_of_id name) (List.map snd args) (ret_type t)
  in
  let bb =
    append_block llcontext "entry" fun_
  in
  let () = 
    List.iter (uncurry (vardef context)) @@
      List.combine (List.map fst args) (Array.to_list @@ params fun_)
  in
  let () =
    position_at_end bb builder
  in
  let ret =
    generate_value context body
  in
  let () = 
    ignore (build_ret ret builder)
  in
  dump_value fun_;
  Llvm_analysis.assert_valid_function fun_

let f (Closure.Prog(funs, body)) =
 let llcontext =
    Llvm.global_context ()
  in
  let builder =
    Llvm.builder llcontext
  in
  let module_ = 
    create_module llcontext "mincaml_module"
  in
  let table =
    Hashtbl.create 0
  in
  let context =
    { llcontext; builder; module_; table }
  in
  let _ =
    flip M.iter !Typing.extenv begin fun name (Type.Fun (ts,t)) ->
      let name = 
        "min_caml_" ^ name
      in
      ignore @@ declare_fun context name ts t
    end
  in
  let () = 
    List.iter (generate_function context) funs
  in
  let () =
    generate_function context {
      Closure.name = (Id.L "min_caml_start", Type.Fun([], Type.Unit));
      args         = []; 
      formal_fv    = []; 
      body
    }
  in
  context.module_
