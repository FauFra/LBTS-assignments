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
  | Fun of string * expr   
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

type history_list = symbol list

type value =
  | Int of int
  | Closure of string * expr * value env
  | RecClosure of string * string * expr * value env

(* Type returned by eval *)
type ret_val = value * policy_stack * history_list


let rec lookup env x =
  match env with
  | []        -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup r x


(* 
  Check if the dfa is well formed
*)
let well_formed_dfa policy =
  let rec check_transitions transitions sigma = 
    match transitions with
    | [] -> true
    | (_, sym, _)::xs -> if (List.mem sym sigma) then check_transitions xs sigma else false
  in let rec check_accepting accepting states =
    match accepting with
    | [] -> true
    | s::xs -> if (List.mem s states) then check_accepting xs states else false
  in let check_start start states = List.mem start states
in (check_transitions policy.transitions policy.sigma) && (check_accepting policy.accepting policy.states) && (check_start policy.start policy.states)

(* 
  Transact to new state in the dfa. 
  If symbol is not in the list of transistions then it doesn't produce a change of the state.
*)
let rec new_state (current_state : state) (symbol : symbol) (transitions : transition list) : state = 
  match transitions with
  | [] -> current_state
  | (s,sym, new_s)::xs -> 
    if (s = current_state && sym = symbol) then 
    new_s else new_state current_state symbol xs

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
  

let rec eval (e : expr) (env : value env) (pol_stack: policy_stack) (his : history_list) : ret_val =
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
        |  _ -> failwith "unknown primitive or wrong type"
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
  | RecFun(x, funDef, funCall) ->
      begin
        match funDef with
          |Fun(arg, fBody) -> 
            let rec_fun = RecClosure(x, arg, fBody, env) in
            let new_env = (x, rec_fun)::env in
            eval funCall new_env pol_stack his
          |_ -> failwith("non functional def")
      end
  | Call(eFun, eArg) ->let (fClosure, _, _) = eval eFun env pol_stack his in
      begin
        match fClosure with
        | Closure (x, fBody, fDeclEnv) ->
            let (xVal, new_pol_stack, new_his) = eval eArg env pol_stack his in
            let fBodyEnv = (x, xVal) :: fDeclEnv
            in eval fBody fBodyEnv new_pol_stack new_his
        | RecClosure(x, fArg, fBody, fDeclEnv) ->
            let (aVal, new_pol_stack, new_his) = eval eArg env pol_stack his in
            let rEnv = (x,fClosure)::env in (* ambiente con la chiusura ricorsiva *)
            let aEnv = (fArg, aVal)::rEnv in (* ambinete con il bind tra parametro attuale e argomento della funzione*)
            eval fBody aEnv new_pol_stack new_his
        | _ -> failwith "eval Call: not a function"
      end 
  | Frame(policy, body) -> 
    if not(well_formed_dfa policy) then
      failwith "Malformed policy"
    else
      let (current_state, accepted) = check_history policy his
      in
        if(accepted) then
          let (value, _, new_his) = eval body env ((current_state,policy)::pol_stack) his
          in (value, pol_stack, new_his)
        else failwith "Violated policy (frame)"
  | Read x -> 
      let new_pol_stack = check_policy_stack pol_stack Read
      in (Int 1, new_pol_stack, his@[Read])
  | Write(_) -> 
      let new_pol_stack = check_policy_stack pol_stack Write
      in (Int 1, new_pol_stack, his@[Write])
  | Connect x ->
      let new_pol_stack = check_policy_stack pol_stack Connect
      in (Int 1, new_pol_stack, his@[Connect])


(* No write *)
let	no_write	:	dfa	=		
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

(* No read after write *)
let	no_read_after_write	:	dfa	=		
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

let h = [];;
let e0 = [];;
let ps = [];;


(* Connect, no_read_after_write[Read, no_write[Read], Write], Write *)
let frame1 = Frame(no_write, Read("prova"));;
let r0 = Let("q", frame1, Write("x", CstI 1));;
let r1 = Let("y",Read("x"), r0);;
let frame2 = Frame(no_read_after_write, r1);;
let r2 = Let("x", Connect("prova"), frame2);;
let r3 = Let("z", r2, Write("x", CstI 1));;

(* Output: (Int 1, [], [Connect; Read; Read; Write; Write]) *)
eval r3 e0 ps h;;

(* Read, no_read_after_write[Read], Write, no_read_after_write[Read] *)
let frame1 = Frame(no_read_after_write, Read("prova"));;
let r1 = Let("y",Read("x"), frame1);;
let r2 = Let("x", r1, Write("x", CstI 1));;
let frame2 = Frame(no_read_after_write, Read("x"));;
let r3 = Let("z", r2, frame2);;

(* Output: Exception: Failure "Violated policy (check_policy_stack)" *)
eval r3 e0 ps h;;