type permission =
  | ReadPerm
  | WritePerm
  | ExecPerm

type permissions = permission list

type expr =
  | CstI of int
  | CstB of bool
  | Var of string
  | Let of string * expr * expr
  | Prim of string * expr * expr
  | If of expr * expr * expr
  | Fun of string * expr * permissions
  | Call of expr * expr
  | Read of string
  | Write of string * expr
  | Exec of string


(*Run-time*)
type permissions_stack =  permissions list

type 'v env = (string * 'v) list
type value =
  | Int of int
  | Closure of string * expr * permissions * value env 


let rec lookup_env env x =
  match env with
  | []        -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup_env r x


(* Return the permissions of the frame on top of the stack, if it exists. Otherwhise an empty lit *)
let lookup_permissions_stack stack =
  match stack with
  | [] -> []
  | perm::z -> perm


(* Create the intersection between the new frame on top of the stack and the frame below *)
let permissions_frame perm stack = 
  match stack with
  | [] -> perm
  | permissions_list::x -> List.filter (fun p -> List.mem p permissions_list) perm


(* Check if there is some duplicate permission in perm *)
let rec check_well_formed_permissions perm = 
  match perm with
  | [] -> true
  | x::y -> if (List.mem x y)==false then check_well_formed_permissions y else false


(* Check if the permission perm is in the set of the permiossions of the frame on top of the stack *)
let check_permissions perm stack =
  let perm_stack = lookup_permissions_stack stack in
  List.mem perm perm_stack


let rec eval (e : expr) (stack : permissions_stack) (env : value env) : value =
  match e with
  | CstI i -> Int i
  | CstB b -> Int (if b then 1 else 0)
  | Var x  -> lookup_env env x
  | Prim(ope, e1, e2) ->
      let v1 = eval e1 stack env in
      let v2 = eval e2 stack env in
      begin
        match (ope, v1, v2) with
        | ("*", Int i1, Int i2) -> Int (i1 * i2)
        | ("+", Int i1, Int i2) -> Int (i1 + i2)
        | ("-", Int i1, Int i2) -> Int (i1 -i2)
        | ("=", Int i1, Int i2) -> Int (if i1 = i2 then 1 else 0)
        | ("<", Int i1, Int i2) -> Int (if i1 < i2 then 1 else 0)
        |  _ -> failwith "unknown primitive or wrong type"
      end
  | Let(x, eRhs, letBody) ->
      let xVal = eval eRhs stack env in
      let letEnv = (x, xVal) :: env in
      eval letBody stack letEnv
  | If(e1, e2, e3) ->
      begin
        match eval e1 stack env with
        | Int 0 -> eval e3 stack env
        | Int _ -> eval e2 stack env
        | _     -> failwith "eval If"
      end
  | Fun(x,fBody, perm) -> 
      if check_well_formed_permissions perm then 
        Closure(x, fBody, perm, env) 
      else failwith "Not well formed permissions list, duplicate permission"
  | Call(eFun, eArg) ->let fClosure = eval eFun stack env in
      begin
        match fClosure with
        | Closure (x, fBody, perm, fDeclEnv) ->
            let xVal = eval eArg stack env in
            let fBodyEnv = (x, xVal) :: fDeclEnv in
            let perm_frame = permissions_frame perm stack
            in eval fBody (perm_frame::stack) fBodyEnv
        | _ -> failwith "eval Call: not a function"
      end 
  |Read x -> if (check_permissions ReadPerm stack) then Int 1 else failwith "permission denied (read)"
  |Write(_) -> if (check_permissions WritePerm stack) then Int 1 else failwith "permission denied (write)"
  |Exec x -> if (check_permissions ExecPerm stack) then Int 1 else failwith "permission denied (exec)"



let env = []
let perm_stack = []
let fun1 = Fun("x",Exec("prova"),[ExecPerm]);;
let env1 = ("f1", eval fun1 perm_stack env)::env;;
let fun2 = Fun("y",Call(Var "f1", CstI 0), [ReadPerm; ExecPerm]);;
let env2 = ("f2", eval fun2 perm_stack env1)::env1;;
let fun3 = Fun("z",Call(Var "f2", CstI 0), [WritePerm; ReadPerm; ExecPerm]);;
let env3 = ("f3", eval fun3 perm_stack env2)::env2;;
eval (Call(Var "f3", CstI 0)) perm_stack env3;;