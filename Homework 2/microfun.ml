type state = int

type symbol = Read | Write | Connect

type transition = state * symbol * state

type dfa = {
  states: state list;
  sigma: symbol list;
  start: state;
  transitions: transition list;
  accepting: state list;
}

type expr =
  | CstI of int
  | CstB of bool
  | Var of string
  | Let of string * expr * expr
  | Prim of string * expr * expr
  | If of expr * expr * expr
  | Fun of string * expr   (* Lambda , param Body *)
  | RecFun of string * expr * expr
  | Call of expr * expr
  | Frame of dfa * expr
  | Read of string
  | Write of string * expr
  | Connect of string


(* Run-time *)
type 'v env = (string * 'v) list

type policy_frame = state * dfa

type policy_stack = policy_frame list

type history_stack = symbol list

type value =
  | Int of int
  | Closure of string * expr * value env
  | RecClosure of string * (string * expr * value env)

(* Type returned by eval *)
type ret_val = value * policy_stack * history_stack


let rec lookup env x =
  match env with
  | []        -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup r x

(* 
  Transact to new state in the dfa. 
  If symbol is not in the list of transistions then it doesn't produce a change of the state.
*)
let rec new_state (current_state : state) (symbol : symbol) (transitions : transition list) : state = 
  match transitions with
  | [] -> current_state
  | (s,sym, new_s)::xs -> if (s = current_state && sym = symbol) then new_s else new_state current_state symbol xs

(* 
  Return the state of the policy after all the transitions executed by symbols in symbol_list 
*)
let rec exec_policy (current_state:state) (symbol_list: symbol list) (transitions: transition list) : state =
  match symbol_list with
  | [] -> current_state
  | symbol::xs -> exec_policy (new_state current_state symbol transitions) xs transitions

(* 
  Return the couple (end_state, accepted).
  end_state = finale state of the dfa after all the transactions executed by symbols in the history list.
  accepted = boolean that specifies if the end_state is an accepted state
*)
let check_history policy history = 
  let end_state = exec_policy policy.start history policy.transitions
  in 
    if(List.mem end_state policy.accepting) then (end_state,true)
    else (end_state,false)


(*
 Return a new policy_stack with all policies' state updated in base to the symbol op
*)
let rec check_policy_stack (policy_stack : policy_stack) (op : symbol) : policy_stack =
  match policy_stack with 
  | [] -> []
  | (current_state, policy)::xs -> 
      let new_state = exec_policy current_state [op] policy.transitions
      in
        if (List.mem new_state policy.accepting) then (new_state,policy)::(check_policy_stack xs op)
        else failwith "Violated policy (check_policy_stack)"
  

let rec eval (e : expr) (env : value env) (pol_stack: policy_stack) (his : history_stack) : ret_val =
  match e with
  | CstI i -> (Int i, pol_stack, his)
  | CstB b -> (Int (if b then 1 else 0), pol_stack, his)
  | Var x  -> (lookup env x, pol_stack, his)
  | Prim(ope, e1, e2) ->
      let (v1, _, _) = eval e1 env pol_stack his in
      let (v2, _, _) = eval e2 env pol_stack his in
      begin
        match (ope, v1, v2) with
        | ("*", Int i1, Int i2) -> (Int (i1 * i2), pol_stack, his)
        | ("+", Int i1, Int i2) -> (Int (i1 + i2), pol_stack, his)
        | ("-", Int i1, Int i2) -> (Int (i1 -i2), pol_stack, his)
        | ("=", Int i1, Int i2) -> (Int (if i1 = i2 then 1 else 0), pol_stack, his)
        | ("<", Int i1, Int i2) -> (Int (if i1 < i2 then 1 else 0), pol_stack, his)
        |  _ -> failwith "unknown primiRve or wrong type"
      end
  | Let(x, eRhs, letBody) ->
      let (xVal, new_pol_stack, new_his) = eval eRhs env pol_stack his in
      let letEnv = (x, xVal) :: env in
      eval letBody letEnv new_pol_stack new_his
  | If(e1, e2, e3) ->
      begin
        match eval e1 env pol_stack his with
        | (Int 0, new_pol_stack, new_his) -> eval e3 env new_pol_stack new_his
        | (Int _, new_pol_stack, new_his) -> eval e2 env new_pol_stack new_his
        | (_)    -> failwith "eval If"
      end
  | Fun(x,fBody) -> (Closure(x, fBody, env), pol_stack, his)
  | RecFun(x, funDef, body) ->
      begin
        match funDef with
          |Fun(y, fBody) -> 
            let rec_fun = RecClosure(x, (y, fBody, env))
            in
              let new_env = (x, rec_fun)::env
              in eval body new_env pol_stack his
          |_ -> failwith("non functional def")
      end
  | Call(eFun, eArg) ->let (fClosure, _, _) = eval eFun env pol_stack his in
      begin
        match fClosure with
        | Closure (x, fBody, fDeclEnv) ->
            let (xVal, new_pol_stack, new_his) = eval eArg env pol_stack his in
            let fBodyEnv = (x, xVal) :: fDeclEnv
            in eval fBody fBodyEnv new_pol_stack new_his
        | RecClosure(x, (arg, fBody, fDeclEnv)) ->
          let (xVal, new_pol_stack, new_his) = eval eArg env pol_stack his in
          let env_1 = (x,fClosure)::env in
          let env_2 = (arg, xVal)::env_1 in
          eval fBody env_2 new_pol_stack new_his
        | _ -> failwith "eval Call: not a function"
      end 
  |Frame(policy, body) -> 
    let (current_state, accepted) = check_history policy his
    in
      if(accepted) then
        let (value, _, new_his) = eval body env ((current_state,policy)::pol_stack) his
        in (value, pol_stack, new_his)
      else failwith "Violated policy (frame)"
  |Read x -> 
    let new_pol_stack = check_policy_stack pol_stack Read
    in (Int 1, new_pol_stack, his@[Read])
  |Write(_) -> 
    let new_pol_stack = check_policy_stack pol_stack Write
    in (Int 1, new_pol_stack, his@[Write])
  |Connect x ->
    let new_pol_stack = check_policy_stack pol_stack Connect
  in (Int 1, new_pol_stack, his@[Write])


(* no write *)
let	d	:	dfa	=		
{	states	=	[0];	
    sigma	=	[Read; Write];	
    start	=	0;	
    transitions	=	
        [
          (0,Read,0);	
          (0,Write,1)
        ];	
    accepting	=	[0];
}	

let	d1	:	dfa	=		
{	states	=	[0;1;2];	
    sigma	=	[Read; Write];	
    start	=	0;	
    transitions	=	
        [
          (0,Read,0);	
          (0,Write,1);	
          (1,Read,2);	
          (1,Write,1);	
          (2,Read,2);
          (2,Write,2)
        ];	
    accepting	=	[0;1];
}	



let frame1 = Frame(d, Read("prova"));;
let r0 = Let("q", frame1, Write("x", CstI 1));;
let r1 = Let("y",Read("x"), r0);;

let frame2 = Frame(d1, r1);;
let sum = Prim("+", CstI 1, CstI 1);;
let r2 = Let("x", sum, frame2);;

let r3 = Let("z", r2, Write("x", CstI 1));;


let h = [];;
let e0 = [];;
let ps = [];;


eval r3 e0 ps h;;