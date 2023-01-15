


#use "semantic-analyser.ml";;

module type CODE_GEN = sig

  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  val make_fvars_tbl : expr' list -> (string * int) list

  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
   let lelse = ref 0;;
   let lexit = ref 0;;
   let lcont = ref 0;;
   let lcode = ref 0;;
   let lloop = ref 0;;
   let advance_pointer p = p := !p+1
  
    
  let make_consts_tbl asts = 
    let rec get_const exp =
      (match exp with
      | ScmConst'(x) -> (match x with
                            | ScmVector(lst) ->  ((List.flatten (List.map (fun e -> (get_const (ScmConst'(e)))) lst)) @ [x])
                            | ScmPair(car, cdr) -> ((get_const (ScmConst'(car))) @ (get_const (ScmConst'(cdr))) @ [x])
                            | _ -> [x])
      | ScmVar'(x) -> []
      | ScmBox'(x) -> []
      | ScmBoxGet'(x) -> []
      | ScmBoxSet'(x,y) -> get_const y
      | ScmIf'(test, dit, dif) -> (get_const test) @ (get_const dit) @ (get_const dif)
      | ScmSeq'(lst) -> List.flatten (List.map (fun e -> get_const e) lst)
      | ScmSet'(x, y) -> get_const y
      | ScmDef'(x, y) -> get_const y
      | ScmOr'(lst) -> List.flatten (List.map (fun e -> get_const e) lst)
      | ScmLambdaSimple'(args, body) -> get_const body
      | ScmLambdaOpt'(args, first, body) -> get_const body
      | ScmApplic'(rator, rands) -> (get_const rator) @ (List.flatten (List.map (fun e -> get_const e) rands))
      | ScmApplicTP'(rator, rands) -> (get_const rator) @ (List.flatten (List.map (fun e -> get_const e) rands))) in

    let rec make_consts_tbl_help expr_lst  = 
        (match expr_lst with
            | [] -> []
            | first::rest -> (get_const first) @ (make_consts_tbl_help rest)) in

    let rec constIsMember sexp ans = (match ans with 
            | [] -> false
            | first::rest -> (match (sexpr_eq first sexp) with
                                  |true -> true
                                  | _ -> constIsMember sexp rest)) in
    
    let rec remove_dup_from_const_lst lst ans=
        match lst with
          |[] -> ans
          |first::rest -> (match first with
                           |ScmNil -> (remove_dup_from_const_lst rest ans)
                           |ScmVoid -> (remove_dup_from_const_lst rest ans) 
                           |ScmBoolean(a) -> (remove_dup_from_const_lst rest ans) 
                           |_ -> (match (constIsMember first ans) with
                              |false ->  remove_dup_from_const_lst rest (ans @ [first])
                              |_ ->  (remove_dup_from_const_lst rest ans))) in
    
    let rec checkPosition var lst = 
        match lst with
          |[] -> raise X_this_should_not_happen
          |first::rest -> (match first with 
                          |(f, (position, _)) -> (match (sexpr_eq f var) with 
                                                    |true -> position
                                                    |_ -> checkPosition var rest)) in

    let rec createLstForVector lst ans const_tbl = (match lst with
          | [] -> ans
          |[first] -> ans^ "const_tbl + "^(string_of_int(checkPosition first const_tbl))
          |first::rest -> createLstForVector rest (ans^ "const_tbl + "^(string_of_int(checkPosition first const_tbl))^",") const_tbl) in

    let rec create_const_table lst position const_tbl = match lst with 
                  | [] -> const_tbl
                  | first::rest -> (match first with

                                      | ScmVoid ->  create_const_table rest (position + 1) (const_tbl @ [(first, (position, "MAKE_VOID"))])
                                      | ScmNil ->  create_const_table rest (position + 1) (const_tbl @ [(first, (position, "MAKE_NIL"))]) 
                                      | ScmBoolean(b) -> let bo = (match b with
                                                                  |true -> 1
                                                                  |false -> 0)
                                                         in
                                                         create_const_table rest (position + 1 + 1) (const_tbl @ [(first, (position, "MAKE_BOOL("^(string_of_int bo)^")"))])
                                      | ScmChar(ch) -> create_const_table rest (position + 1 + 1) (const_tbl @[(first, (position, "MAKE_LITERAL_CHAR("^ (string_of_int(Char.code ch))^")"))])
                                      | ScmString(str) -> let len = String.length str in
                                                  create_const_table rest (position + 1 + 8 + len) (const_tbl @ [(first, (position, "MAKE_LITERAL_STRING \""^str^"\""))])
                                      | ScmSymbol(str) -> let len = String.length str in 
                                                          let str_insert_tbl = create_const_table [ScmString(str)] position const_tbl in
                                                          let new_position = position + 1 +  8 + len in 
                                                          let finish_position = position + 1 + 8 + 1 +  8 + len in
                                                                  create_const_table rest finish_position 
                                                                  (str_insert_tbl @ [(first, (new_position, "MAKE_LITERAL_SYMBOL(const_tbl + "^(string_of_int(checkPosition (ScmString(str)) str_insert_tbl))^")"))])
                                      | ScmNumber(num) -> (match num with
                                                            | ScmRational(x,y) ->  create_const_table rest (position + 1 + 16) (const_tbl @ [(first, (position, "MAKE_LITERAL_RATIONAL("^(string_of_int x)^","^(string_of_int y)^")"))])
                                                            | ScmReal(x) ->  create_const_table rest (position + 1 + 8) (const_tbl @[(first, (position, "MAKE_LITERAL_FLOAT("^(Float.to_string x)^")"))]))                                                                                        
                                      | ScmVector(lst) -> let len = List.length lst in
                                                          let str_lst = (createLstForVector lst "" const_tbl) in
                                                          create_const_table rest (position + 1 + 8 + 8*len) (const_tbl @ [(first, (position, "MAKE_LITERAL_VECTOR "^str_lst))])
                                      (**fix pair so we activate create_const_table with each one of it parts seperatly (car and cdr) *)
                                      (**vector - 1 byte for tag, 8 bytes for car pointer, 8 bytes for cdr pointer *)
                                      | ScmPair(car,cdr) ->  create_const_table rest (position + 17) (const_tbl @ 
                                                                                                      [(first, (position, "MAKE_LITERAL_PAIR(const_tbl + "^(string_of_int(checkPosition car const_tbl))^
                                                                                                  ",const_tbl + "^(string_of_int(checkPosition cdr const_tbl))^")"))])) in

    
    
    let const_table = make_consts_tbl_help asts in
    let const_table = remove_dup_from_const_lst const_table [] in
    let const_table = [ScmVoid; ScmNil; ScmBoolean(false); ScmBoolean(true)] @ const_table in
    create_const_table const_table 0 []


  let make_fvars_tbl asts = 
     let rec get_fvar exp =
      (match exp with
      | ScmConst'(x) -> []
      | ScmVar'(x) -> (match x with 
                      |VarFree(v) -> [v]
                      |_-> [])
      | ScmBox'(x) -> []
      | ScmBoxGet'(x) -> []
      | ScmBoxSet'(x,y) -> get_fvar y
      | ScmIf'(test, dit, dif) -> (get_fvar test) @ (get_fvar dit) @ (get_fvar dif)
      | ScmSeq'(lst) -> List.flatten (List.map (fun e -> get_fvar e) lst)
      | ScmSet'(x, y) -> (get_fvar y)
      | ScmDef'(VarFree(x), y) -> ((get_fvar y) @ [x])
      | ScmOr'(lst) -> List.flatten (List.map (fun e -> get_fvar e) lst)
      | ScmLambdaSimple'(args, body) -> get_fvar body
      | ScmLambdaOpt'(args, first, body) -> get_fvar body
      | ScmApplic'(rator, rands) -> (get_fvar rator) @ (List.flatten (List.map (fun e -> get_fvar e) rands))
      | ScmApplicTP'(rator, rands) -> (get_fvar rator) @ (List.flatten (List.map (fun e -> get_fvar e) rands))
      | _ -> raise X_this_should_not_happen) in

    let rec make_fvars_tbl_help expr_lst  = (List.flatten (List.map (fun e -> get_fvar e) expr_lst)) in

    
    let rec remove_dup_from_fvars_lst lst ans=
        match lst with
          |[] -> ans
          |first::rest -> (match (List.mem first ans) with

                              | false ->  remove_dup_from_fvars_lst rest (ans @ [first])
                              |_ ->  (remove_dup_from_fvars_lst rest ans)) in
    
    (**we should add here all the fvar methods that are not in code and then append it to the create const table while index will be the last index 
     we probable don't need to do it because the expr' list that we get is built from stdlib.scm appended with the infile.scm*)
    let rec create_fvars_table lst index = 
        (match lst with
          | [] -> []
          | first::rest -> [(first, index)] @ (create_fvars_table rest (index + 1))) in
                   
    let fvar_tbl = make_fvars_tbl_help asts in
    let fvar_tbl = remove_dup_from_fvars_lst fvar_tbl [] in
    let primitive_labels =  [
              (* Type queries  *)
              "boolean?"; "flonum?"; "rational?";
              "pair?"; "null?"; "char?"; "string?";
              "procedure?"; "symbol?";
              (* String procedures *)
              "string-length"; "string-ref"; "string-set!";
              "make-string"; "symbol->string";
              (* Type conversions *)
              "char->integer"; "integer->char"; "exact->inexact";
              (* Identity test *)
              "eq?";
              (* Arithmetic ops *)
              "+"; "*"; "/"; "="; "<";
              (* Additional rational numebr ops *)
              "numerator"; "denominator"; "gcd";
              (* you can add yours here *)
              "car"; "cdr"; "apply"; "cons";"set-car!"; "set-cdr!"
            ] in
    let fvar_tbl = primitive_labels @ fvar_tbl in
    let fvar_tbl = remove_dup_from_fvars_lst fvar_tbl [] in    
    create_fvars_table fvar_tbl 0

    
  let generate consts fvars e = 
      let rec gen exp env_depth =
      (match exp with
          | ScmConst'(x) -> "mov rax, const_tbl +"^string_of_int(constOffsetInConsts x consts)^ "; insert const from const table to rax"
          | ScmVar'(x) -> (match x with
                          |VarParam(_,minor) -> "mov rax, qword [rbp + " ^string_of_int(8 * ( 4 + minor))^ "]"
                          |VarBound(_,major, minor) -> "mov rax, qword [rbp + 8*2]
                                                              \n mov rax, qword[rax +" ^string_of_int(8 * major)^ "]
                                                              \n mov rax, qword[rax +" ^string_of_int(8 * minor)^ "]"
                          |VarFree(v) -> "mov rax, qword [fvar_tbl + " ^string_of_int(8 * (varIndexInFvar v fvars))^ "]")
          | ScmBox'(x) -> generate_box x env_depth
          | ScmBoxGet'(x) -> generate_box_get x env_depth
          | ScmBoxSet'(x,y) -> generate_box_set x y env_depth
          | ScmIf'(test, dit, dif) -> generate_if test dit dif env_depth
          | ScmSeq'(lst) -> (List.fold_left (fun a b -> a^(gen b env_depth)^"\n") "" lst)
          | ScmSet'(x, y) -> (match x with
                          |VarParam(_,minor) -> (gen y env_depth)^
                                                              "\n mov qword [rbp + " ^string_of_int(8 * ( 4 + minor))^ "], rax
                                                              \n mov rax, SOB_VOID_ADDRESS"
                          |VarBound(_,major, minor) ->(gen y env_depth)^
                                                            "\n mov rbx, qword [rbp + 8*2]
                                                              \n mov rbx, qword [rbx +" ^string_of_int(8 * major)^"]
                                                              \n mov qword[rbx +" ^string_of_int(8 * minor)^"], rax
                                                              \n mov rax SOB_VOID_ADDRESS"
                          |VarFree(v) -> (gen y env_depth)^
                                                "\n mov qword [fvar_tbl + " ^string_of_int(8*(varIndexInFvar v fvars))^ "], rax
                                                  \n mov rax, SOB_VOID_ADDRESS")
          | ScmDef'(x, y) -> (match x with
                          |VarFree(v) -> generate_def v y env_depth
                          |_ -> raise X_not_yet_implemented)
          | ScmOr'(lst) ->  let _ = (advance_pointer lexit) in
                            let str = generate_or lst "" env_depth in                      
                            str                       
          | ScmLambdaSimple'(args, body) -> let _ = (advance_pointer lcode) in
                                            let _ =  (advance_pointer lcont) in 
                                            (generate_lambda_simple args body env_depth)
          | ScmLambdaOpt'(args, first, body) -> let _ = (advance_pointer lcode) in
                                                let _ =  (advance_pointer lcont) in 
                                              (generate_lambda_opt args first body env_depth)
          | ScmApplic'(rator, rands) -> let _ = (advance_pointer lexit) in
                                        (generate_applic rator rands env_depth)
          | ScmApplicTP'(rator, rands) -> let _ = (advance_pointer lexit) in 
                                          (generate_applic_tp rator rands env_depth))
      
      and generate_if test dit dif env_depth = 
            let else_label = "Lelse"^(string_of_int (!lelse)) in
            let _ = (advance_pointer lelse) in
            let exit_label = "Lexit"^(string_of_int (!lexit)) in
            let _ = (advance_pointer lexit) in
            let gen_test = gen test env_depth in
            let gen_dit = gen dit env_depth in
            let gen_dif = gen dif env_depth in
            ";                  generate if\n"^             
            gen_test ^
            "\n cmp rax, SOB_FALSE_ADDRESS
             \n je "^else_label^"\n"^
             gen_dit^
             "\n jmp "^exit_label^"\n"^
             else_label^":\n"^
             gen_dif^"\n"^
             exit_label^":
             ;                  finish generate if"


      and generate_applic rator rands env_depth =
            let gen_rands = (List.map (fun e -> gen e env_depth) rands) in
            let rands_num = List.length gen_rands in
            let gen_rands = (List.fold_left (^) "" (List.rev (List.map (fun e -> e ^ "\npush rax\n") gen_rands))) in
            let gen_rator = gen rator env_depth in
            let label_exit = "Exit_applic_"^ (string_of_int !lexit) in
            let _ = (advance_pointer lexit) in
            ";                  generate applic\n"^
            "push SOB_NIL_ADDRESS ; magic\n"^
            gen_rands ^ "
            push " ^ (string_of_int rands_num) ^ "  ; number of args\n" ^
            gen_rator ^ "
            mov rsi, rax  ; move the rator to rsi
            mov bl, byte [rsi]
            cmp bl, T_CLOSURE
            jne "^ label_exit ^ "
            CLOSURE_ENV rsi, rax
            push rsi ;push env
            CLOSURE_CODE rsi, rax
            call rsi ;call code
            add rsp, 8*1 ;pop Env
            pop rbx ;pop arg count   
            add rbx, 1 ; including magic    
            shl rbx, 3 ;rbx=rbx*8
            add rsp,rbx ;pop args\n"^
            label_exit^":
            ;                     finish generate applic"

    and generate_applic_tp rator rands env_depth =
            let label_exit = "Exit_applic_"^ (string_of_int !lexit) in
            let loop_label = "Loop"^(string_of_int !lloop) in
            let change_label = "Change"^(string_of_int !lloop) in

            let _ = (advance_pointer lexit) in
            let _ = (advance_pointer lloop) in
            let _ = (advance_pointer lloop) in

            let gen_rands = (List.map (fun e -> gen e env_depth) rands) in
            let gen_rands = (List.rev gen_rands) in
            let rands_num = List.length gen_rands in
            let gen_rands = (List.map (fun e -> e^"\npush rax\n") gen_rands) in
            let gen_rands = (List.fold_left (^) "" gen_rands) in
            let gen_rator = gen rator env_depth in
            ";                  generate applic tp\n"^
            "push SOB_NIL_ADDRESS ; magic \n"^
            gen_rands ^ "
            push " ^ (string_of_int rands_num) ^ ";    push number of rands to stack
             ;                  gen rator
            "^gen_rator ^ "
            mov rsi, rax
            mov bl, byte [rsi]
            cmp bl, T_CLOSURE         ; check if rax is clouser
            jne "^ label_exit ^ "
            CLOSURE_ENV rsi, rax      ; get env from closure
            push rsi                  ; push env
            push qword [rbp + 8 * 1]  ; old ret addr

            ;                       fixing the stack
            push qword[rbp]
            mov rsi, rax              ; mov closure pointer to rsi
            mov rax, rbp              ; save rbp in rax
            mov r8, [rbp+3*8]         ; arg count
            ;;sub r8, 1                 ; we want to get arg i in place i-1
            add r8, 4 
            shl r8, 3
            add rax, r8      
            mov rcx, rbp              ; rcx address first obj of this stack
            sub rcx, 8 \n"^
            loop_label ^ ":
              cmp rcx, rsp            ;end of new stack
              jl " ^ change_label ^ "
              mov rbx, [rcx]
              mov [rax], rbx
              sub rcx, 8
              sub rax, 8
              jmp " ^ loop_label ^ "\n" ^
            change_label ^ ":
              mov rsp, rax
              add rsp, 8
              pop rbp
            ;                       finish fixing the stack

        CLOSURE_CODE rsi, rsi
        jmp rsi                    ; push env, call code \n"^
        label_exit ^ ":
        ;                           finish generate applic tp"


    and generate_def var value env_depth = 
          let gen_value = gen value env_depth in
          let var_ind = varIndexInFvar var fvars in
          ";                      generate define\n"^
          gen_value ^ "\n" ^
          "mov [fvar_tbl+" ^ (string_of_int var_ind) ^ "*WORD_SIZE], rax ; insert var to free var table\n" ^
          "mov rax, SOB_VOID_ADDRESS ; define return void
          ;                       finish generate def"


  and generate_lambda_simple args body env_depth =
        let code_label = "Lcode"^(string_of_int (!lcode)) in
        let _ = (advance_pointer lcode) in
        let cont_label = "Lcont"^(string_of_int (!lcont)) in
        let _ = (advance_pointer lcont) in
        let arg_len = (List.length args) in
         ";                   generate lambda simple
         MALLOC rax, "^ (string_of_int (8* (env_depth+1)))^" ; rax is pointer to _ env"^
        "\n
         push rbx
         push rdx
         mov qword rbx, [rbp + 8*2] ; get curr env" ^ 
        (makeEnv 0 1 env_depth "")^ 
        "\n push rax ; save pointer to _ env
          \n; MALLOC rax, "^(string_of_int(8 * arg_len + 1))^"; num of params
         mov rcx, [rbp + 8*3]     ;;father function argc
         lea rax, [8*rcx]
         MALLOC rax, rax    ;;pointer to new params array
         cmp rcx, 0
         je .end_loop
         mov r9, 0
         .loop:
            mov r10, [rbp + 8*(4+r9)]
            mov [rax + 8*r9], r10
            inc r9
            loop .loop
          .end_loop:
         "^
        "\n mov rdx, rax
         \n pop rax
         \n mov qword [rax], rdx ; insert pointer to param's arr to _ env[0]
         \n pop rdx 
         \n pop rbx
         \n push r8
         \n mov r8, rax"^
         "\n MAKE_CLOSURE(rax ,r8, "^code_label^")"^         
        "\n pop r8
         \n jmp "^cont_label^
        "\n "^code_label^":"^
            "\n push rbp
             \n mov rbp, rsp
             \n "^(gen body (env_depth+1))^
            "\n leave
             \n ret
         \n "^cont_label^":
         ;                    finish generate lambda simple"

    and generate_lambda_opt args first body env_depth =
        let arg_len = (List.length args) in
        let cont_label = "Lcont"^(string_of_int (!lcont)) in
        let _ = (advance_pointer lcont) in
        let code_label = "Lcode"^(string_of_int (!lcode)) in
        let _ = (advance_pointer lexit) in
        
         "\n ; generate lambda opt
          \n MALLOC rax, "^ (string_of_int (8* (env_depth+1)))^
        "\n push rbx
         \n push rdx
         \n mov qword rbx, [rbp + 8*2]\n" ^ 
        (makeEnv 0 1 env_depth "")^ 
        "\n push rax
         mov rcx, [rbp + 8*3 ]            ;;father function argc
         ;inc rcx
         lea rax, [8*rcx]
         MALLOC rax, rax                  ;;pointer to new params array
         cmp rcx, 0
         je .end_loop
         mov r9, 0
         .loop:
            mov r10, [rbp + 8*(4+r9)]
            mov [rax + 8*r9], r10
            inc r9
            loop .loop
          .end_loop:

         "^
         
        "\n mov rdx, rax
         \n pop rax
         \n mov qword [rax], rdx
         \n pop rdx 
         \n pop rbx
         \n push r8
         \n mov r8, rax
         \n MAKE_CLOSURE (rax , r8, "^code_label^")"^
        "\n pop r8
         \n jmp "^cont_label^
        "\n "^code_label^":
             \n push rbp
             \n mov rbp, rsp
             \n push rdx
             \n push rcx
             \n push rbx
             \n push rax"^
            "\n OPT_PARAMS "^(string_of_int(arg_len))^", SOB_NIL_ADDRESS"^
            "\n mov qword [rbp+8*(4 + "^(string_of_int(arg_len))^")], rdx
             \n pop rax
             \n pop rbx
             \n pop rcx
             \n pop rdx

             \n "^(gen body (env_depth+1))^
            "\n leave
             \n ret
         \n "^cont_label^":"

  and makeEnv i j env_depth str =
      if( i < env_depth) then
        makeEnv (i+1) (j+1) env_depth (str ^"\n mov qword rdx, [rbx +" ^string_of_int (i*8)^"]
                                       \n mov qword [rax+ "^string_of_int(j*8)^"], rdx" )
                    else
                    str

  and generate_or lst ans env_depth = 
        let exit_label = "Lexit"^(string_of_int (!lexit)) in
        (generate_or_help lst ans env_depth exit_label) 

  and generate_or_help lst ans env_depth exit_label = (match lst with
                      |[] -> ans^"\n"^exit_label^":"
                      |[first] -> generate_or_help [] (ans^(gen first env_depth)^"\n") env_depth exit_label
                      |first::rest -> generate_or_help rest (ans^(gen first env_depth)^"\ncmp rax, SOB_FALSE_ADDRESS
                                                                \n jne "^exit_label^"\n") env_depth exit_label)
        
                                  

  and generate_box var env_depth = 
        let gen_var = gen (ScmVar'(var)) env_depth in
        gen_var ^
       "\n MALLOC rbx, 8
        \n mov qword[rbx], rax
        \n mov rax, rbx
        "


  and generate_box_get var env_depth = 
        let gen_var = gen (ScmVar'(var))  env_depth in
        gen_var ^ "
        \n mov rax, qword [rax]
        "

  and generate_box_set var vl env_depth = 
        let gen_var = gen (ScmVar'(var)) env_depth in
        let gen_val = gen vl env_depth in
        gen_val ^ 
        "\n push rax\n" ^ 
        gen_var ^ 
        "\n pop qword [rax]    
         \n mov rax, SOB_VOID_ADDRESS"        
        
  and constOffsetInConsts sexp const_tbl = 
    (match const_tbl with 
        |[] -> raise X_this_should_not_happen
        |first::rest -> (match first with
              |(sexpr, (offset, asm_str)) -> (match (sexpr_eq sexpr sexp) with
                          | true -> offset
                          | _ -> constOffsetInConsts sexp rest))) 


  and varIndexInFvar var fVar_table = 
    (match fVar_table with 
        |[] -> raise X_this_should_not_happen
        |first::rest -> (match first with
              |(name,pointer) -> (match (String.compare name var) with
                          | 0 -> pointer
                          | _ -> varIndexInFvar var rest))) in
  
  gen e 0

      
end;;

