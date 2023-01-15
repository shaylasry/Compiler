(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


(**parrent matching - if both v1 and v2 are the same sub type of var' - free,bound,param
   check if both are the same var. we check for the major and minor for bound*)
let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

(**pattern matching for two expr' from same type *)
let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr' 
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

(**lookup in rib pass all the params and check if we found the same
name in the parms list. we run on the rib list and check for "name"
if we couldn't find it we reuten None type. *)
(**lookup in rib -> we check the params list from stack *)
  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

(**search the name in all the prev env's. check rib in each 1.
if we got None and there are still env in the env array we got to the next env *)
(*lookup in env -> go to the env pointer and start checking the name in all env's*)
  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

(**shay comment
  this method get a var name' params list and env pointer
  then we tag the lexical address for name var according to:
  search it in the params list and if found bound it to be varParam
  else -> search it in the env and bound it according to where it been spoted
  else -> make it a VarFree *)
  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;


  let annotate_lexical_addresses pe = 
   let rec run pe params env = match pe with
        | ScmConst (expr) -> ScmConst'(expr)
        | ScmVar(name) -> ScmVar'(tag_lexical_address_for_var name params env)
        | ScmIf(test, dit, dif) -> ScmIf'((run test params env), (run dit params env), (run dif params env)) 
        | ScmSeq (list) -> ScmSeq'(List.map (fun ex -> run ex params env) list) 
        | ScmSet (var, valu) -> ScmSet'((tag_lexical_address_for_var (string_of_expr(var)) params env) , (run valu params env))
        | ScmDef (var, valu) -> ScmDef'((tag_lexical_address_for_var (string_of_expr(var)) params env), (run valu params env))
        | ScmOr (list) -> ScmOr'(List.map (fun ex -> run ex params env) list) 
        | ScmLambdaSimple(args ,body) -> ScmLambdaSimple'(args,(run body args (params::env)))
        | ScmLambdaOpt(args,first,body) -> ScmLambdaOpt'(args, first, (run body (args @ [first]) (params::env)))
        | ScmApplic(expr, exprs) -> ScmApplic'((run expr params env), (List.map (fun ex -> run ex params env) exprs))
   in 
   run pe [] [];;



  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
      (match pe with
      | ScmConst'(expr) -> pe
      | ScmVar'(name) -> pe
      | ScmIf'(test,dit,dif) -> ScmIf'((run test false), (run dit in_tail), (run dif in_tail))
      | ScmSeq'(list) -> 
          let breakList = rdc_rac list in
          (match breakList with
          |(a,b) ->
          let headList = (a) in
          let tail = (b) in
          ScmSeq'((List.map (fun ex -> run ex false) headList) @ [(run tail in_tail)]))
      | ScmSet'(var, valu) -> ScmSet'(var,(run valu false))
      | ScmDef'(var, valu) -> ScmDef'(var,(run valu false))
      | ScmOr'(list)-> 
          let breakList = rdc_rac list in
          (match breakList with
          |(a,b) ->
          let headList = (a) in
          let tail = (b) in
          ScmOr'((List.map (fun ex -> run ex false) headList) @ [(run tail in_tail)]))
      | ScmLambdaSimple' (args, body) -> ScmLambdaSimple' (args, (run body true))
      | ScmLambdaOpt' (args, first, body) -> ScmLambdaOpt' (args, first, (run body true))
      | ScmApplic'(expr, exprs)-> (match in_tail with
                                  |true -> ScmApplicTP'(run expr false,(List.map (fun ex -> run ex false) exprs) )
                                  |false ->  ScmApplic'( run expr in_tail , List.map (fun ex-> run ex false) exprs))
      | _ -> raise X_this_should_not_happen)   
   in 
   run pe false;;




  (* boxing *)



  let rec shouldBox var enclosing_lambda =  
    match enclosing_lambda with
    |ScmLambdaSimple'(args, body) -> (
                let reads =  find_reads var enclosing_lambda body true in   
                let writes = find_writes var enclosing_lambda body true in
                let boxTerm read write_list1 = 
                  (match read with
                  | [read_var1, read_lambda1] -> 
                      let check_list = (List.map 
                                    (fun write ->
                                      (match write with
                                      | [write_var, write_lambda] ->if(read_lambda1 == write_lambda) 
                                                 then false
                                                 else true
                                               
                                      | _ -> raise X_this_should_not_happen))
                                      write_list1) 
                      in
                      (isTrueInLst check_list)
                  | _ -> raise X_this_should_not_happen)
                    
                     (* (List.mem true check_list)  *)
                in

                let checkForBox read_list write_list =
                    List.map (fun (read) ->
                      (match read with
                      | [read_var, read_lambda] ->  (boxTerm [read_var, read_lambda] write_list)
                      | _ -> raise X_this_should_not_happen))
                       reads in
                    (isTrueInLst (checkForBox reads writes))

                (* (List.mem true (checkForBox reads writes)) *)
              )
    |ScmLambdaOpt'(args,first, body) -> (
                let reads = find_reads var enclosing_lambda body true in   
                let writes = find_writes var enclosing_lambda body true in
                let boxTerm read write_list1 = 
                  (match read with
                  | [read_var1, read_lambda1] -> let check_list = (List.map 
                  (fun write -> 
                  (match write with
                  | [write_var, write_lambda] -> if(read_lambda1 == write_lambda) 
                      then false
                      else true
                  | _ -> raise X_this_should_not_happen))
                    write_list1) in
                    (isTrueInLst check_list)
                  | _ -> raise X_this_should_not_happen)
                    
                     (* (List.mem true check_list)  *)
                in

                let checkForBox read_list write_list =
                    List.map (fun (read) -> 
                    (match read with
                    | [read_var, read_lambda] -> (boxTerm [read_var, read_lambda] write_list) 
                    | _ -> raise X_this_should_not_happen))  reads in
                    (isTrueInLst (checkForBox reads writes))
                (* (List.mem true (checkForBox reads writes)) *)
              )
    | _ -> raise X_this_should_not_happen
and isTrueInLst lst = (match lst with
    | [] -> false
    | [first] -> (match first with
              |true -> true
              |_ -> false)
    | first::rest -> (match first with
              |true -> true
              |_ -> isTrueInLst rest))

and find_reads name enclosing_lambda expr isFirstLambda = match expr with
    | ScmConst'(x) -> []
    | ScmVar'(x) -> (match x with
        |VarFree(y) -> []
        |VarParam(y,minor) -> (match (String.equal name y) with 
                                    | true -> [[x ,enclosing_lambda]]
                                    | _ -> [])
        |VarBound(y,i,minor) -> (match (String.equal name y) with 
                                    | true -> [[x ,enclosing_lambda]]
                                    | _ -> []))
    | ScmBoxGet'(x) -> []
    | ScmBoxSet'(x, y) -> find_reads name enclosing_lambda y isFirstLambda
    | ScmIf'(test, dit, dif) -> (find_reads name enclosing_lambda test isFirstLambda) @ (find_reads name enclosing_lambda dit isFirstLambda) @ (find_reads name enclosing_lambda dif isFirstLambda)
    | ScmSeq'(list) -> List.flatten (List.map (fun e -> find_reads name enclosing_lambda e isFirstLambda) list)
    | ScmSet'(var, value) -> find_reads name enclosing_lambda value isFirstLambda
    | ScmDef'(var, value) -> find_reads name enclosing_lambda value isFirstLambda
    | ScmOr'(list) -> List.flatten (List.map (fun e -> find_reads name enclosing_lambda e isFirstLambda) list)
    | ScmLambdaSimple'(args, body) -> 
    (* (match (List.mem name args) with *)
                                        (match (isMemberInLstStr name args) with
                                        |true -> []
                                        | _ ->  (match isFirstLambda with
                                                    |true -> find_reads name expr body false
                                                    |_ -> find_reads name enclosing_lambda body false)
                                      )
    | ScmLambdaOpt'(args, first, body) -> 
    (* (match (List.mem name (args @ [first])) with *)
                                       (match (isMemberInLstStr name (args @ [first])) with
                                              | true -> []
                                              | _ -> (match isFirstLambda with
                                                    |true -> find_reads name expr body false
                                                    |_ -> find_reads name enclosing_lambda body false)
                                            )
    | ScmApplic'(rator, rands) -> (find_reads name enclosing_lambda rator isFirstLambda) @ (List.flatten (List.map (fun e -> find_reads name enclosing_lambda e isFirstLambda) rands))
    | ScmApplicTP'(rator, rands) -> (find_reads name enclosing_lambda rator isFirstLambda) @ (List.flatten (List.map (fun e -> find_reads name enclosing_lambda e isFirstLambda) rands))
    | _ -> raise X_this_should_not_happen

  and isMemberInLstStr var lst = (match lst with
    | [] -> false
    | [first] -> (String.equal first var) 
    | first::rest -> (match (String.equal first var) with
            |true -> true
            | _ -> (isMemberInLstStr var rest)))
                      


  and find_writes name enclosing_lambda expr isFirstLambda = match expr with
    | ScmConst'(x) -> []
    | ScmVar'(x) -> []
    | ScmBoxGet'(x) -> []
    | ScmBoxSet'(x, y) -> find_writes name enclosing_lambda y isFirstLambda
    | ScmIf'(test, dit, dif) -> (find_writes name enclosing_lambda test isFirstLambda) @ (find_writes name enclosing_lambda dit isFirstLambda) @ (find_writes name enclosing_lambda dif isFirstLambda)
    | ScmSeq'(list) -> List.flatten (List.map (fun e -> find_writes name enclosing_lambda e isFirstLambda) list)
    | ScmSet'(var, value) -> (match var with
                                | VarFree(x) -> find_writes name enclosing_lambda value isFirstLambda
                                | VarBound(x, y, z) -> (match (String.equal x name) with
                                                      | true -> [[var, enclosing_lambda]] @(find_writes name enclosing_lambda value isFirstLambda)
                                                      | _ -> find_writes name enclosing_lambda value isFirstLambda)
                                | VarParam(x, y) -> (match (String.equal x name) with
                                                      | true -> [[var, enclosing_lambda]] @(find_writes name enclosing_lambda value isFirstLambda)
                                                      | _ -> find_writes name enclosing_lambda value isFirstLambda)
                              )
    | ScmDef'(var, value) -> find_writes name enclosing_lambda value isFirstLambda
    | ScmOr'(list) -> List.flatten (List.map (fun e -> find_writes name enclosing_lambda e isFirstLambda) list)
    | ScmLambdaSimple'(args, body) -> 
    (* (match (List.mem name args) with *)
        (match (isMemberInLstStr name args) with

                                        |true -> []
                                        | _ -> (match isFirstLambda with
                                                |true -> find_writes name expr body false
                                                |_ -> find_writes name enclosing_lambda body false)
                                              )
    | ScmLambdaOpt'(args, first, body) -> 
    (* (match (List.mem name (args @ [first])) with *)
    (match (isMemberInLstStr name (args @ [first])) with
                                        | true -> []
                                        | _ -> (match isFirstLambda with
                                                  |true -> find_writes name expr body false
                                                  |_ -> find_writes name enclosing_lambda body false)
                                      )
    | ScmApplic'(rator, rands) -> (find_writes name enclosing_lambda rator isFirstLambda) @ (List.flatten (List.map (fun e -> find_writes name enclosing_lambda e isFirstLambda) rands))
    | ScmApplicTP'(rator, rands) -> (find_writes name enclosing_lambda rator isFirstLambda) @ (List.flatten (List.map (fun e -> find_writes name enclosing_lambda e isFirstLambda) rands))
    | _ -> raise X_this_should_not_happen

   
 
  let apply_box args body enclosing_lambda = (match body with
    | [] -> []
    | (first::rest) -> (List.filter (fun arg -> shouldBox arg enclosing_lambda) body))


  let rec applied_changes name expr = match expr with
        | ScmConst'(x) -> expr 
        | ScmVar'(x) -> (match x with
            |VarFree(v) -> expr
            |VarParam(v,minor)-> if (String.equal v name) then ScmBoxGet'(x) else expr
            |VarBound(v,major,minor)-> if (String.equal v name) then ScmBoxGet'(x) else expr)
        | ScmBoxGet'(x) -> expr
        | ScmBoxSet'(x, y) -> ScmBoxSet'(x, applied_changes name y)
        | ScmIf'(test, dit, dif) -> ScmIf'(applied_changes name test, applied_changes name dit, applied_changes name dif)
        | ScmSeq'(list) -> ScmSeq'(List.map (fun a -> applied_changes name a) list)
        | ScmSet'(var, value) -> (match var with 
            |VarFree(v) -> ScmSet'(var, applied_changes name value)
            |VarParam(v,minor)-> if (String.equal v name) then ScmBoxSet'(var,applied_changes name value) else ScmSet'(var, applied_changes name value)
            |VarBound(v,major,minor)-> if (String.equal v name) then ScmBoxSet'(var,applied_changes name value) else ScmSet'(var, applied_changes name value))
        | ScmDef'(var, value) -> ScmDef'(var, applied_changes name value) 
        | ScmOr'(list) -> ScmOr'(List.map (fun a -> applied_changes name a) list)
        | ScmLambdaSimple'(args, body) -> ( if (isMemberInLstStr name args) then expr 
                                                                    else ScmLambdaSimple'(args, applied_changes name body)
                              )
        | ScmLambdaOpt'(args, first, body) -> ( if (isMemberInLstStr name (args @ [first])) then expr 
                                                                    else ScmLambdaOpt'(args, first, applied_changes name body)
                              )  
        | ScmApplic'(rator, rands) -> ScmApplic'(applied_changes name rator, (List.map (fun a -> applied_changes name a) rands)) 
        | ScmApplicTP'(rator, rands) -> ScmApplicTP'(applied_changes name rator, (List.map (fun a -> applied_changes name a) rands))
        | _ -> raise X_this_should_not_happen

  let rec findMinor x lst =
          match lst with
          | [] -> -1
          | h :: t -> if x = h then 0 else 1 + findMinor x t


  let rec box_set expr = match expr with
        | ScmConst'(x) -> expr 
        | ScmVar'(x) -> expr
        | ScmBoxGet'(x) -> expr
        | ScmBoxSet'(x, y) -> expr
        | ScmIf'(test, dit, dif) -> ScmIf'(box_set test, box_set dit, box_set dif)
        | ScmSeq'(list) -> ScmSeq'(List.map (fun a -> box_set a) list)
        | ScmSet'(var, value) -> ScmSet'(var, box_set value)
        | ScmDef'(var, value) -> ScmDef'(var, box_set value) 
        | ScmOr'(list) -> ScmOr'(List.map (fun a -> box_set a) list)
        | ScmLambdaSimple'(args, body) -> (
                                    let shouldBoxLst = (List.filter (fun arg -> (shouldBox arg expr)) args) in
                                    (match shouldBoxLst with
                                    |[] -> ScmLambdaSimple'(args,(box_set body))
                                    |_ -> let newBody = List.fold_left (fun acc curr -> applied_changes curr acc) body shouldBoxLst in (*apply changes on body *) 
                                          let startBody = List.fold_left (fun acc curr -> acc @ [ScmSet'(VarParam(curr, findMinor curr args), ScmBox'(VarParam(curr, findMinor curr args)))]) [] shouldBoxLst in (* add the box set lines *)

                                          (match newBody with
                                            | ScmSeq'(lst) ->  ScmLambdaSimple'(args, ScmSeq'(startBody @ (List.map (fun n -> box_set n) lst)))
                                            |_ ->  ScmLambdaSimple'(args, ScmSeq'(startBody @ [box_set newBody])))
                                         ) 

                              )
        | ScmLambdaOpt'(args,first, body) -> (
                                    let shouldBoxLst = (List.filter (fun arg -> (shouldBox arg expr)) (args @ [first])) in
                                    (match shouldBoxLst with
                                    |[] -> ScmLambdaOpt'(args,first, (box_set body))
                                    |_ -> let newBody = List.fold_left (fun acc curr -> applied_changes curr acc) body shouldBoxLst in (*apply changes on body *) 

                                          let startBody = List.fold_left (fun acc curr -> acc @ [ScmSet'(VarParam(curr, findMinor curr (args@[first])), ScmBox'(VarParam(curr, findMinor curr (args@[first]))))]) [] shouldBoxLst in (* add the box set lines *)
                                          (match newBody with 
                                              | ScmSeq'(lst) ->  ScmLambdaOpt'(args,first, ScmSeq'(startBody @ (List.map (fun n -> box_set n) lst)))
                                              |_ ->  ScmLambdaOpt'(args,first, ScmSeq'(startBody @ [box_set newBody])))
                                         ) 
                              )           

        | ScmApplic'(rator, rands) -> ScmApplic'(box_set rator, (List.map (fun a -> box_set a) rands)) 
        | ScmApplicTP'(rator, rands) -> ScmApplicTP'(box_set rator, (List.map (fun a -> box_set a) rands))
        | _ -> raise X_this_should_not_happen

       
        

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
