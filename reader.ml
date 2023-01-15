
 #use "pc.ml";;

 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 
 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool     
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
 
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; 
 
 module Reader : READER = struct
 (* module Reader  = struct *)
 
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 let nt_digit_0_to_9 = 
      pack (range '0' '9') 
       (let ascii_0 = int_of_char '0' in
       (fun ch -> (int_of_char ch) - ascii_0))
 
 let nt_digit_0_to_9_float = 
      pack (range '0' '9') 
       (let ascii_0 = int_of_char '0' in
       (fun ch -> (float_of_int((int_of_char ch) - ascii_0))))
 
 let nt_natural =
     let rec nt str =
     pack (caten nt_digit_0_to_9
           (disj nt nt_epsilon))
           (function (a, s) -> a :: s) str in
           pack nt
           (fun s ->
           (List.fold_left
           (fun a b -> 10 * a + b)
           0
           s));;
           
 let make_float_right s =
   let float_list =(List.map
                   (fun x -> float_of_int(x))
                   s) in 
   let rev_list =  (List.rev float_list) in
             (List.fold_left
               (fun a b -> (a +. b) /. 10.0)
               0.0
               rev_list);;  
 
 
  
 
 
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str
 and nt_line_comment str = 
   let nt_end = disj(unitify (char '\n')) (unitify nt_end_of_input) in
   let nt1 = char ';' in
   let nt2 = diff nt_any nt_end in
   let nt2 = star nt2 in
   let nt1 = caten nt1 (caten nt2 nt_end) in
   let nt1 = unitify nt1 in
   nt1 str
 and nt_paired_comment str = 
 let nt1 = char '{' in
   let nt2 = disj_list [unitify nt_char; unitify nt_string; nt_comment] in
   let nt0 = disj nt2 (unitify (one_of "{}")) in
   let nt3 = diff nt_any nt0 in
   let nt3 = disj (unitify nt3) nt2 in
   let nt3 = star nt3 in
   let nt4 = char '}' in
   let nt1 = unitify (caten nt1 (caten nt3 nt4)) in
   nt1 str
 and nt_sexpr_comment str = 
   let nt1 = word "#;" in
   let nt2 = caten nt1 nt_sexpr in
   let nt2 = unitify nt2 in
   nt2 str
 and nt_comment str =
   disj_list
     [nt_line_comment;
      nt_paired_comment;
      nt_sexpr_comment] str
 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str
 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1
 and nt_int str = 
   let nt_plus_or_minus = disj (char '+') (char '-') in
   let nt1 =  caten (maybe nt_plus_or_minus) nt_natural in
   let nt1 = pack nt1 (fun (op,num) -> 
                             match op with
                             |None -> num
                             |Some op_ch -> if(op_ch = '-') then -num else num) in
   nt1 str
 
 and nt_frac str = 
   let nt1 = char '/' in
   let nt1 = caten nt_int (caten nt1 nt_natural) in
   let nt1 = pack nt1 (fun (up ,(ch ,down)) -> 
                             let devisor = gcd up down in
                             ScmRational ((up/devisor),(down/devisor))) in
   nt1 str
 and nt_integer_part str = 
   nt_natural str 
 and nt_mantissa str = 
   plus nt_digit_0_to_9 str   
 and nt_exponent str = 
   let nt_exp_char = disj_list [(word_ci "e"); (word "*10^"); (word "*10**")]  in
   let nt1 = pack (caten nt_exp_char nt_int) 
         (fun (a,b) -> b) in
   nt1 str
 and nt_float str = 
   let nt1 = char '.' in
   let nt1 = caten (pack nt_integer_part (fun num -> float_of_int num)) (caten nt1 (caten (maybe nt_mantissa) (maybe nt_exponent))) in
   let nt1 = pack nt1 
             (fun (left, (dot, (mantis, exp))) -> match mantis with
                                                  |None -> (match exp with
                                                           |None -> left
                                                           |Some ex -> left *. (10.0**float_of_int(ex)))
                                                  |Some man -> (match exp with
                                                           |None -> left +. (make_float_right man)
                                                           |Some ex -> ((left +.(make_float_right man)) *. (10.0**float_of_int(ex))))) in
   let nt2 = char '.' in
   let nt2 = caten nt2 (caten nt_mantissa (maybe nt_exponent)) in
   let nt2 = pack nt2
             (fun (dot, (mantis, exp)) -> match exp with
                                          |None -> (make_float_right mantis)
                                          |Some ex -> ((make_float_right mantis) *. (10.0**float_of_int(ex)))) in
   let nt3 = caten nt_integer_part nt_exponent in
   let nt3 = pack nt3 
             (fun (num, exp)-> float_of_int(num) *. (10.0**float_of_int(exp))) in                                                 
   let nt_plus_or_minus = disj (char '+') (char '-') in
   let nt4 =  caten (maybe nt_plus_or_minus) (disj_list [nt1; nt2; nt3]) in
   let nt4 = pack nt4  (fun (op,num) -> 
                             match op with
                             |None -> ScmReal (num)
                             |Some op_ch -> if(op_ch = '-') then ScmReal (-.num) else ScmReal(num)) in                                                
   nt4 str
 and nt_number str =
   let nt1 = nt_float in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 (disj nt2 nt3) in
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 and nt_boolean str =  
   let nt1 = word_ci "#f" in
   let nt1 = pack nt1 (fun _ -> false) in
   let nt2 = word_ci "#t" in
   let nt2 = pack nt2 (fun _ -> true) in
   let nt1 = disj nt1 nt2 in
   let nt1 = pack nt1 (fun b -> ScmBoolean b) in
   nt1 str
 and nt_char_simple str = 
 let nt1 = range '\032' '\127' in
 nt1 str
 (* let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);; *)
 and make_named_char char_name ch = 
 let nt1 = word_ci char_name in
 pack nt1 (fun _ -> ch) 
 
     
 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t');
                (make_named_char "nul" '\000')] in
   nt1 str
 
 and nt_char_hex2 str =  
 
 let nt1 = range '0' '9' in
   let nt1 = pack nt1 
                 (let delta = int_of_char '0' in
                 fun ch -> (int_of_char ch) - delta) in
   let nt2 = range 'a' 'f' in
   let nt2 = pack nt2 
                 (let delta = int_of_char 'a' - 10 in
                 fun ch -> (int_of_char ch) - delta) in
   let nt3 = range 'A' 'F' in
   let nt3 = pack nt3 
                 (let delta = int_of_char 'A' - 10 in
                 fun ch -> (int_of_char ch) - delta) in              
   let nt2 = disj nt1 (disj nt2 nt3) in
   let nt2 = plus nt2 in
   let nt2 = pack nt2
                   (fun digits -> 
                       List.fold_left
                           (fun a b -> 16*a + b)
                           0
                           digits) in
   let nt2 = pack nt2  (fun (b) -> char_of_int b) in                  

   nt2 str 
 and nt_char str = 
   let nt_c_hex = pack (caten (char_ci 'x') nt_char_hex2)   
                  (fun (a,b) -> b) in
   let nt1  = word_ci "#\\" in
   let nt1 = caten nt1 (disj_list [nt_c_hex;  nt_char_named; nt_char_simple;]) in
   let nt2 = pack nt1
             (fun (_,ch) -> ScmChar(ch)) in
   nt2 str 
 
 and nt_symbol_char str = 
 let nt1 = disj_list [(range '/' ':'); (range '<' '?'); (range 'A' 'Z'); 
                      (range 'a' 'z'); char '!'; char '$'; char '^'; 
                      char '*'; char '-'; char '_'; char '+'] in
 nt1 str
       
 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str
 and nt_string str = 
   let nt_string_literal_char = disj_list [(range (char_of_int 0) (char_of_int 33)) ; 
                                           (range (char_of_int 35) (char_of_int 91)) ; 
                                           (range (char_of_int 93) (char_of_int 125)) ; 
                                           (char (char_of_int 127))] in
   let nt_string_literal_char = pack nt_string_literal_char (fun ch -> ScmString (String.make 1 ch))  in
 
 
   let nt_backslash = char_ci (char_of_int 92) in
   
   let nt_string_meta_char = disj_list[(caten nt_backslash nt_backslash); 
                                       (caten nt_backslash (char_ci '\"')); 
                                       (caten nt_backslash (char_ci 't')); 
                                       (caten nt_backslash (char_ci 'f')); 
                                       (caten nt_backslash (char_ci 'n')); 
                                       (caten nt_backslash (char_ci 'r')); 
                                       (caten (char_ci '~') (char_ci '~'));] in
                              
   let nt_string_meta_char = pack nt_string_meta_char (fun (_ , ch) -> 
                                 if(ch = '\\') then "\\"
                                 else if(ch = '\"') then "\""
                                 else if(ch = 't') then "\t"
                                 else if(ch = 'f') then "\012"
                                 else if(ch = 'n') then "\n"
                                 else if(ch = 'r') then "\r"
                                 else "~"
                                 ) in
   let nt_string_meta_char = pack nt_string_meta_char (fun s -> ScmString (s)) in
  
   let nt_string_hex_char = pack (caten (caten nt_backslash (char_ci 'x')) (caten (plus nt_char_hex2) (char ';')))   
                  (fun ((a,x),(b,c)) -> ScmString (List.fold_left (fun acc curr -> acc^(Char.escaped(curr))) "" b)) in 

 
   let nt_prefix = word_ci "~{" in
   let nt_postfix = char_ci '}' in
   let nt_string_interpolated = caten nt_prefix (caten nt_sexpr nt_postfix) in
   let nt_string_interpolated = pack nt_string_interpolated (fun (_, (sexpr, _)) -> ScmPair((ScmSymbol "format"), ScmPair((ScmString "~a"),  ScmPair (sexpr, ScmNil)))) in
            
   
   let nt_double_quote = char '\"' in
   let nt_double_quote = pack nt_double_quote (fun ch -> ScmString (Char.escaped ch)) in
   let nt_static = disj_list[
           nt_string_hex_char;
           nt_string_literal_char;
           nt_string_meta_char;
           ] 
           in
   
   let nt = disj_list[
           nt_static;
           nt_string_interpolated;
   ] in
 
 
   let nt = caten nt_double_quote (caten (star nt) nt_double_quote) in
   let nt = pack nt (fun (_, (lst,_)) -> lst) in
   let nt = pack nt (fun lst -> 
               List.fold_right
                (fun curr acc  ->
                   (match curr with 
                   |ScmPair (car, cdr) ->
                     (match acc with 
                       | ScmNil -> ScmPair(curr, acc)
                       | _ -> ScmPair(curr, acc))
 
                   |ScmString(s) ->
                     (match acc with 
                       |ScmNil ->  ScmPair(ScmString(s), ScmNil)           
                       |ScmPair(ScmString(x), ScmNil) -> ScmPair(ScmString(s^x), ScmNil) 
                       |ScmPair(ScmString(x), y) -> ScmPair(ScmString(s^x), y)
                       |ScmPair(x,y) -> ScmPair(curr, acc)
                       |_ -> raise X_no_match
                       )
                   | _ -> raise X_no_match)
                 )
                lst
                ScmNil
   ) in
   let nt = pack nt (fun res ->
                       match res with
                       |ScmPair(ScmString(x), ScmNil) -> ScmString(x)
                       |ScmPair(ScmPair(x,y), ScmNil) -> ScmPair(x,y)
                       |_ -> ScmPair(ScmSymbol("string-append"), res)
               ) in
   let nt_empty_string = pack (word "\"\"") (fun _ -> ScmString("")) in
   let nt = disj nt_empty_string nt in
   nt str
 
 and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str
  
 
 
 and nt_list str =
   let nt_skip = disj (unitify nt_whitespace) nt_comment in
   let nt_skip = unitify (star nt_skip) in
   let nt_left_bracket = pack (caten nt_skip (caten (char_ci '(') nt_skip)) (fun (a, (b, c)) -> b)  in
   let nt_right_bracket = pack (caten nt_skip (caten (char_ci ')') nt_skip)) (fun (a, (b, c)) -> b) in
   let rec orginaize_func list = match list with
                             | [] -> ScmNil
                             | (sexp::[]) -> ScmPair(sexp, ScmNil)
                             | (sexpr::sexp) -> ScmPair (sexpr ,(orginaize_func sexp)) in
   let nt_proper_list = caten nt_left_bracket (caten (star nt_sexpr) nt_right_bracket) in
   let nt_proper_list = pack nt_proper_list (fun (a,(b,c)) ->
                                             orginaize_func b) in
   let nt_dot = char_ci '.' in
   let rec orginaize_func_2 a b = match a with
                           | (sexpr :: []) -> ScmPair(sexpr, b)
                           | (c::d) -> ScmPair (c ,(orginaize_func_2 d b))
                           |_ -> raise X_no_match
                    in
   let orginaize_func_3 = (fun (_ , (a, (_ , (b, _)))) ->
                             orginaize_func_2 a b) in
 
   let nt_improper_list = caten nt_left_bracket (caten (plus nt_sexpr) (caten nt_dot (caten nt_sexpr nt_right_bracket))) in
   let nt_improper_list = pack nt_improper_list  orginaize_func_3 in
   let nt = disj nt_proper_list nt_improper_list in
   nt str
 
   
 and make_quoted_forms sign sym_string str= 
 let nt_quote = plus (word sign) in
 let nt_quote = caten nt_quote nt_sexpr in
 let nt_quote = pack nt_quote 
            (fun (list, tail) ->  (List.fold_left
                                   (fun a b -> ScmPair((nt_symbol sym_string 0).found, ScmPair (a, ScmNil)))
                                   tail
                                   list)
                                     ) in
 nt_quote str
 and nt_quoted_forms str = 
 let nt_quote = make_quoted_forms  "\'" "quote" in
 let nt_quasi_quote = make_quoted_forms  "`" "quasiquote" in
 let nt_unqoute = make_quoted_forms  "," "unquote" in
 let nt_unquote_splicing = make_quoted_forms ",@" "unquote-splicing" in
 let nt1 = disj_list [nt_quote; nt_quasi_quote; nt_unqoute; nt_unquote_splicing] in
 nt1 str
 
 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;; 
 
 end;; (* end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;
 