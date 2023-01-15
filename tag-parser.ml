#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;
exception X_not_good;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;


                                                


let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in



match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 

(* Implement tag parsing here *)
| ScmNil -> (ScmConst(ScmNil))  
| ScmBoolean(b) -> (ScmConst(ScmBoolean(b)))
| ScmChar(ch) -> (ScmConst(ScmChar(ch))) 
| ScmNumber(n) -> (ScmConst(ScmNumber(n)))
| ScmString(s) -> (ScmConst(ScmString(s)))
| ScmVector(lst) -> (ScmConst(ScmVector(lst)))
| ScmPair(ScmSymbol("quote"),ScmPair(x,ScmNil)) -> ScmConst(x)
| ScmSymbol(var) -> (match (ormap (fun r -> r = var) reserved_word_list) with
                      |false -> ScmVar(var)
                      |_ -> raise (X_reserved_word (var)))                                 
| ScmPair(ScmSymbol("if"),ScmPair(test, ScmPair(dit ,ScmPair(dif,ScmNil)))) -> 
            ScmIf((tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif))
| ScmPair(ScmSymbol("if"),ScmPair(test, ScmPair(dit ,ScmNil))) -> 
            ScmIf((tag_parse_expression test, tag_parse_expression dit, ScmConst(ScmVoid)))
                                               
| ScmPair(ScmSymbol("or"),cond) -> (match cond with 
                                  |ScmNil -> ScmConst(ScmBoolean(false))
                                  |ScmPair(c,ScmNil) -> (tag_parse_expression c)
                                  |_ -> ScmOr(List.map (fun rib -> tag_parse_expression rib) (scm_list_to_list cond)))
| ScmPair(ScmSymbol("begin"), exps) -> (match exps with
                                  | ScmNil -> ScmConst(ScmVoid)
                                  | ScmPair(first, ScmNil) -> tag_parse_expression first
                                  | _ -> ScmSeq(make_exp_list exps))
| ScmPair(ScmSymbol("set!"), exps) -> (match exps with
                                  | ScmPair(ScmSymbol(x), ScmPair(value, ScmNil)) ->  (ScmSet(ScmVar(x), (tag_parse_expression value)))
                                  | _ -> raise (X_syntax_error(exps, "Syntax not fit to set!")))

 
 | ScmPair(ScmSymbol("lambda"),ScmPair(arg,body))-> 
    let body_list = 
          (match body with
            |ScmPair(body_1, body_rest) -> tag_parse_expression (ScmPair(ScmSymbol("begin"),body))
            |_ -> raise (X_syntax_error(sexpr,"body lambda no found"))    
          ) in
    (match arg with
      |ScmNil -> ScmLambdaSimple([] , body_list)
      |ScmSymbol(a) -> ScmLambdaOpt([],a , body_list)
      |ScmPair(first,rest) ->   
          if scm_is_list arg then
                let arg_list = (List.map (fun argu -> string_of_sexpr argu) (scm_list_to_list arg)) in
                ScmLambdaSimple(arg_list,body_list)       
            else 
                let rec scm_improper_to_list = (function
                        | ScmPair (hd, tl) -> hd::(scm_improper_to_list tl)
                        | _-> []) in
                let rec return_last = (function
                        | ScmPair (hd, tl) -> return_last tl
                        | sexpr -> string_of_sexpr sexpr) in
                ScmLambdaOpt((List.map (fun argu -> string_of_sexpr argu) (scm_improper_to_list arg)), return_last arg,body_list)
      | _ -> raise (X_syntax_error(arg, "Not supposed to happen"))
      )                                 


|ScmPair(ScmSymbol("define"), ScmPair(ScmSymbol(var), ScmPair(vl,ScmNil))) -> 
  if (var = "define") then 
      raise (X_syntax_error(sexpr,"Expected variable on LHS of define"))
 else 
     ScmDef(tag_parse_expression (ScmSymbol(var)), tag_parse_expression vl) 

|ScmPair(ScmSymbol("define"), ScmPair(ScmPair(var, arg), body)) ->  
  if ((string_of_sexpr var) = "define") then 
      raise (X_syntax_error(sexpr,"Expected variable on LHS of define"))
  else 
      ScmDef(tag_parse_expression var, tag_parse_expression (ScmPair(ScmSymbol("lambda") ,ScmPair(arg,body))))


| ScmPair(expr, exprs) -> (match expr with 
                                  |ScmSymbol(x) -> (match (ormap (fun r -> r = x) reserved_word_list) with
                                            | false -> ScmApplic(ScmVar(x), (make_exp_list exprs))
                                            | _ -> raise (X_reserved_word x))
                                  | _ -> ScmApplic(tag_parse_expression expr, (make_exp_list exprs)))
  
  | _ -> ScmConst(ScmNil)



and make_exp_list sexpr = match sexpr with 
      | ScmNil -> []
      | ScmPair (e,p) -> (tag_parse_expression e) :: (make_exp_list p)
      | exp -> [tag_parse_expression exp]
  
                                
                                                                 
                                             
and macro_expand sexpr =
match sexpr with
| ScmPair(ScmSymbol("cond"), ribs) -> (macro_expand_cond ribs)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(value, ScmNil)) -> (macro_expand_quasiquote value) 
| ScmPair(ScmSymbol("and"),value) -> (macro_expand_and value)
| ScmPair(ScmSymbol("let"),rest) -> (macro_expand_let rest)
| ScmPair(ScmSymbol("let*"),rest) -> (macro_expand_let_star rest)
| ScmPair(ScmSymbol("letrec"),rest) -> (macro_expand_letrec rest)
(* Handle macro expansion patterns here *)
| _ -> sexpr


and macro_expand_cond ribs_sexpr = match ribs_sexpr with
    | ScmNil -> ScmNil
    | ScmPair(ScmPair(ScmSymbol("else"), exps), rest) ->  (match exps with
                                                                  | ScmNil -> raise (X_syntax_error(exps, "Cant have Nil after else"))
                                                                  | _ -> ScmPair(ScmSymbol("begin"), exps))

    | ScmPair (ScmPair (test, ScmPair (ScmSymbol ("=>"), ScmPair (f, ScmNil))), rest) ->
      macro_expand (ScmPair
                (ScmSymbol("let"),
                ScmPair
                  (ScmPair
                    (ScmPair (ScmSymbol("value"), ScmPair (test, ScmNil)),
                    ScmPair
                      (ScmPair
                        (ScmSymbol("f"),
                        ScmPair
                          (ScmPair
                            (ScmSymbol("lambda"),
                            ScmPair (ScmNil, ScmPair (f, ScmNil))),
                          ScmNil)),
                      ScmPair
                        (ScmPair
                          (ScmSymbol("rest"),
                          ScmPair
                            (ScmPair
                              (ScmSymbol("lambda"),
                              ScmPair (ScmNil, ScmPair ( macro_expand_cond rest, ScmNil))),
                            ScmNil)),
                        ScmNil))),
                  ScmPair
                    (ScmPair
                      (ScmSymbol("if"),
                      ScmPair
                        (ScmSymbol("value"),
                        ScmPair
                          (ScmPair
                            (ScmPair (ScmSymbol("f"), ScmNil),
                            ScmPair (ScmSymbol("value"), ScmNil)),
                          ScmPair (ScmPair (ScmSymbol("rest"), ScmNil), ScmNil)))),
                    ScmNil))))
    | ScmPair (ScmPair (test, exps), ScmNil) -> ScmPair (ScmSymbol ("if"), ScmPair (test, ScmPair (ScmPair (ScmSymbol ("begin"), exps), ScmNil)))
    | ScmPair (ScmPair (test, exps), rest) -> ScmPair (ScmSymbol ("if"), ScmPair (test, ScmPair (ScmPair (ScmSymbol ("begin"), exps), ScmPair (macro_expand_cond rest, ScmNil))))
    | _ -> raise (X_syntax_error(ribs_sexpr, "Not valid cond expression"))
  
  and macro_expand_quasiquote value = match value with 
    | ScmNil -> ScmPair(ScmSymbol("quote"), ScmPair(ScmNil,ScmNil))
    | ScmSymbol(x) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol(x), ScmNil))
    | ScmPair(ScmSymbol("unquote"), ScmPair(exp, ScmNil)) -> exp
    | ScmPair(ScmSymbol("unquote-splicing"), ScmPair(exp, ScmNil)) -> ScmPair(ScmSymbol("quote"), ScmPair(value,ScmNil))
    | ScmVector(v) -> ScmPair(ScmSymbol("list->vector"),ScmPair((macro_expand_quasiquote (list_to_proper_list v)),ScmNil))
    | ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(exp, nil)) , rest) -> ScmPair(ScmSymbol("append"), ScmPair(exp, ScmPair((macro_expand_quasiquote rest), ScmNil)))
    | ScmPair(a, ScmPair(ScmSymbol("unquote-splicing"), ScmPair(s, ScmNil))) -> ScmPair(ScmSymbol("cons"), ScmPair((macro_expand_quasiquote a), ScmPair(s, ScmNil)))
    | ScmPair(a, b) -> ScmPair(ScmSymbol("cons"), ScmPair((macro_expand_quasiquote a), ScmPair((macro_expand_quasiquote b), ScmNil)))
    | _ -> value
and macro_expand_and value = match value with
    | ScmNil -> ScmBoolean(true)
    | ScmPair(first, ScmNil) -> first
    | ScmPair(car,cdr) -> ScmPair(ScmSymbol("if"), ScmPair(car, ScmPair((macro_expand_and cdr), ScmPair(ScmBoolean(false), ScmNil))))
    |_ -> value

and macro_expand_let rest = (match rest with
    |ScmNil -> raise (X_syntax_error(rest, "not valid let expression"))
    |ScmPair(args,body) -> (match body with
      |ScmNil -> raise (X_syntax_error(rest, "not valid let expression"))
      |_ -> (match args with
            |ScmNil -> ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,body)),ScmNil)
            |ScmPair(f, r) ->
                  (let arg_names = scm_map 
                  (fun (pair) -> 
                  (match pair with
                  | ScmPair(a,ScmPair(_,ScmNil)) -> a
                  | _ -> (raise X_not_good))) args in
                  let arg_vals = scm_map (fun (pair) -> 
                  (match pair with
                  | ScmPair(_,ScmPair(v,ScmNil)) -> v
                  | _ -> (raise X_not_good))) args in
                  ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(arg_names,body)),arg_vals))
            |_ -> raise (X_syntax_error(rest, "That shouldnt happen"))
    ))
    | _ -> raise X_not_good)


and macro_expand_let_star rest = 
    (match rest with
    |ScmNil -> raise (X_syntax_error(rest, "not valid let expression"))
    |ScmPair(args,body) -> (match body with
      |ScmNil -> raise (X_syntax_error(rest, "not valid let expression"))
      |_ -> (match args with 
              |ScmNil -> macro_expand_let rest
              |ScmPair(f,ScmNil) -> macro_expand_let rest
              |ScmPair(f,r) -> macro_expand_let (ScmPair(ScmPair(f,ScmNil), ScmPair(ScmPair(ScmSymbol("let*"),ScmPair(r,body)),ScmNil)))
              | _ -> raise X_not_good
      ))
    | _ -> raise X_not_good)  


and macro_expand_letrec rest = match rest with
  |ScmNil -> raise (X_syntax_error(rest, "not valid let expression"))
  |ScmPair(args,body) -> (match body with
                            |ScmNil -> raise (X_syntax_error(rest, "not valid let expression"))
                            |_ -> (match args with
                                      |ScmNil -> macro_expand_let rest
                                      |ScmPair(f, r) ->
                                            let arg_names = scm_map 
                                            (fun (pair) -> 
                                            (match pair with
                                              | ScmPair(a,ScmPair(_,ScmNil)) -> a
                                              | _ -> (raise X_not_good))) args in
                                            let arg_vals = scm_map 
                                            (fun (pair) -> 
                                              (match pair with
                                              | ScmPair(_,ScmPair(v,ScmNil)) -> v
                                              | _ -> (raise X_not_good))) args in
                                            let var_list = whatever_let arg_names in
                                            let val_list = set_list arg_names arg_vals in 
                                            let body_list = scm_append val_list body in
                                            macro_expand_let (ScmPair(var_list, body_list))
                                      | _ -> raise (X_syntax_error(args,  "Not supposed to happen"))
                                  )
                 )
  | _ -> raise X_not_good
  (* | _ -> raise (X_syntax_error(rest,  "Not supposed to happen")) *)


and set_list var vals = (scm_zip (fun vr vl -> ScmPair(ScmSymbol("set!"),ScmPair(vr,ScmPair(vl,ScmNil)))) var vals)
and whatever_let var = scm_map (fun vr -> ScmPair(vr,ScmPair(ScmPair(ScmSymbol("quote"),ScmPair(ScmSymbol("whatever"),ScmNil)),ScmNil))) var

end;; 

