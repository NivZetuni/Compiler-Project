#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

  let string_to_ascii_list str =
    if ( str = "") then "''" 
    else
      let chars = string_to_list str in
      let asciis_list = List.map (Printf.sprintf "%d") (List.map Char.code chars) in
      let output = String.concat ", "asciis_list in
      output;;

  let rec get_const_list ast =
    match ast with
    | ScmConst'(sexp) -> [sexp]
    | ScmIf' (test, dit, dif) -> List.append (get_const_list test) (List.append (get_const_list dit) ( get_const_list dif))
    | ScmSeq' (expList) -> List.fold_left(fun list expr -> List.append list (get_const_list expr)) [] expList
    | ScmSet' (_var, value) -> get_const_list value
    | ScmBoxSet'(_var, value) -> get_const_list value
    | ScmDef'(_var, value) -> get_const_list value
    | ScmOr' (expList) -> List.fold_left(fun list expr -> List.append list (get_const_list expr)) [] expList
    | ScmLambdaSimple' (_vars, expr) -> get_const_list expr
    | ScmLambdaOpt' (_vars, _var, expr) -> get_const_list expr
    | ScmApplic'(op, valsList) -> List.append (get_const_list op) (List.fold_left(fun list expr -> List.append list (get_const_list expr)) [] valsList)
    | ScmApplicTP' (op, valsList) -> List.append (get_const_list op) (List.fold_left(fun list expr -> List.append list (get_const_list expr)) [] valsList)
    | other -> [] ;;

  let remove_dup list = List.rev (List.fold_left (fun list obj -> if List.mem obj list then list else obj :: list) [] list);;


  let expand sexp =
    match sexp with
    | ScmSymbol(str) -> [ScmString(str); ScmSymbol(str)]
    | ScmPair(first, second) -> [first; second; ScmPair(first, second)]
    | ScmVector(list) -> List.fold_right (fun obj newList -> obj :: newList) list [ScmVector(list)]
    | sexpr -> [sexpr];;

  let rec expansion prev_list list =
    if list = prev_list
      then list
      (* expanding every obj in the list, then delte dup, then enter rec *)
      else expansion list (remove_dup(List.fold_left (fun newList obj -> List.append newList (expand obj)) [] list ))
      ;;

  let check_size sexp =
  match sexp with
    | ScmVoid -> 1
    | ScmNil -> 1
    | ScmBoolean (_) -> 2
    | ScmChar (_) -> 2
    | ScmString (str) -> 9 + String.length str
    | ScmSymbol (_) -> 9
    | ScmNumber(ScmRational (_)) -> 17
    | ScmNumber(ScmReal (_)) -> 9
    | ScmVector (list) -> 9 + ((List.length list) * 8 )
    | ScmPair(_) -> 17;;

  let rec add_offsets consts_list offset =
    match consts_list with
      | [] -> []
      | head :: tail -> let newOffset = offset + check_size head in
                        (head, offset) :: (add_offsets tail newOffset);;
  
  let rec find_offset table sexp =
  match table with
    | [] -> 0
    | (currSexp, offset ) :: tail -> if currSexp = sexp
                                        then offset
                                        else find_offset tail sexp;;

  let rec get_vector_lit list table = 
  match list with
    | [] -> ""
    | head :: [] -> "const_tbl+"^(string_of_int(find_offset table head))
    | head :: tail -> "const_tbl+"^(string_of_int(find_offset table head))^", "^(get_vector_lit tail table);;


  let get_asm_code sexp table = 
    match sexp with
    | ScmVoid -> "db T_VOID"
    | ScmNil -> "db T_NIL"
    | ScmBoolean (bool) -> if bool then "db T_BOOL, 1" else "db T_BOOL, 0"
    | ScmChar (ch) -> Printf.sprintf "MAKE_LITERAL_CHAR (%s)" (string_of_int (int_of_char ch))
    | ScmString (str) -> Printf.sprintf "MAKE_LITERAL_STRING %s" (string_to_ascii_list str )
    | ScmNumber(ScmRational(int1, int2)) -> Printf.sprintf "MAKE_LITERAL_RATIONAL(%d, %d)" int1 int2
    | ScmNumber(ScmReal(float)) -> Printf.sprintf "MAKE_LITERAL_FLOAT (%f)" float
    | ScmSymbol (symb) -> Printf.sprintf "MAKE_LITERAL_SYMBOL (const_tbl+%d)" (find_offset table (ScmString(symb)))
    | ScmPair(head, tail) -> Printf.sprintf "MAKE_LITERAL_PAIR (const_tbl+%d, const_tbl+%d)" (find_offset table head) (find_offset table tail)
    | ScmVector (list) -> Printf.sprintf "MAKE_LITERAL_VECTOR %s" (get_vector_lit list table)
    ;;
  
  let rec add_asm_code table org_table =
  match table with
    | [] -> []
    | (sexp, offset ) :: tail -> (sexp, (offset, get_asm_code sexp org_table)) :: (add_asm_code tail org_table);;
                                        

  let rec to_consts_tbl consts =
    let consts_and_offset = add_offsets consts 0 in
    add_asm_code consts_and_offset consts_and_offset;;



  
  let rec find_offset_constns_table table sexp =
    match table with
      | [] -> 0
      | (currSexp, (offset, _code) ) :: tail -> if currSexp = sexp
                                          then offset
                                          else find_offset_constns_table tail sexp;;
        
  let rec find_offset_fvar_table table name =
    match table with
      | [] -> 0
      | (curr_name, offset) :: tail -> if curr_name = name
                                              (* *8??? *)
                                          then (offset * 8)
                                          else find_offset_fvar_table tail name;;


let rec get_fvar_list ast = match ast with
    | ScmVar'(VarFree(v)) -> [v]
    | ScmIf' (test, dit, dif) -> List.append (get_fvar_list test) (List.append (get_fvar_list dit) (get_fvar_list dif))
    | ScmSeq' (expList) -> List.fold_left(fun list expr -> List.append list (get_fvar_list expr)) [] expList
    | ScmSet' (var, value) -> List.append (get_fvar_list (ScmVar'(var))) (get_fvar_list value)
    | ScmBoxSet'(var, value) -> List.append (get_fvar_list (ScmVar'(var))) (get_fvar_list value)
    | ScmDef'(var, value) -> List.append (get_fvar_list (ScmVar'(var))) (get_fvar_list value)
    | ScmOr' (expList) -> List.fold_left(fun list expr -> List.append list (get_fvar_list expr)) [] expList
    | ScmLambdaSimple' (_vars, expr) -> get_fvar_list expr
    | ScmLambdaOpt' (_vars, _var, expr) -> get_fvar_list expr
    | ScmApplic'(op, valsList) -> List.append (get_fvar_list op) (List.fold_left(fun list expr -> List.append list (get_fvar_list expr)) [] valsList)
    | ScmApplicTP' (op, valsList) -> List.append (get_fvar_list op) (List.fold_left(fun list expr -> List.append list (get_fvar_list expr)) [] valsList)
    | other -> [];;


let primitive_names=
  [
    (* Type queries  *)
    "boolean?"; "flonum?"; "rational?"; "number?";
    "pair?"; "null?"; "char?"; "string?"; "zero?";
    "procedure?"; "symbol?"; "integer?"; "list?";
    (* String procedures *)
    "string-length"; "string-ref"; "string-set!";
    "make-string"; "symbol->string"; "string->list";
    (* Type conversions *)
    "char->integer"; "integer->char"; "exact->inexact";
    (* Identity test *)
    "eq?"; "equal?";
    (* Arithmetic ops *)
    "+"; "*"; "-"; "/"; "<"; "="; ">";
    (* Additional rational numebr ops *)
    "numerator"; "denominator"; "gcd";
    (* you can add yours here *)
    "append"; "apply"; "car"; "cdr"; "cons"; "cons*"; "fold-left"; "fold-right"; 
    "length"; "list"; "map"; "not"; "set-car!"; "set-cdr!";
  ];;

  

let rec to_fvar_table names offset = 
    match names with
    | [] -> []
    | head::tail -> (head,offset) :: (to_fvar_table tail (offset+1))

let label_counter = ref 0;;
(* let inc_counter = label_counter := (!label_counter + 1) ;; *)
let get_counter counter = counter := (!counter + 1); string_of_int !counter;;

let rec gen consts fvars e env_num =
    match e with
    | ScmConst'(sexp) -> Printf.sprintf "mov rax, const_tbl+%d \n" (find_offset_constns_table consts sexp)
    | ScmVar' (VarFree(name)) -> Printf.sprintf "mov rax, qword[fvar_tbl+%d] \n" (find_offset_fvar_table fvars name)
    | ScmVar' (VarParam(_name, minor)) ->  Printf.sprintf "mov rax, qword[rbp + 8*(4+%d)] \n" minor
    | ScmVar' (VarBound(_name, major, minor)) ->  Printf.sprintf "mov rax, qword[rbp + 8*2] \n mov rax, qword[rax + 8*%d] \nmov rax, qword[rax + 8*%d] \n" major minor
    | ScmSet'(VarParam(_,minor), exp) -> (Printf.sprintf "%s \n mov qword [rbp + 8*(4+%d)],rax \n"(gen consts fvars exp env_num) minor)^ "mov rax, SOB_VOID_ADDRESS \n"  
    | ScmSet'(VarBound(_,major,minor), exp) -> (Printf.sprintf "%s \n mov rbx, qword[rbp +8 * 2] \n" (gen consts fvars exp env_num))^ 
                                                          (Printf.sprintf "mov rbx, qword[rbx + 8*%d] \n"  major)^
                                                          (Printf.sprintf "mov qword [rbx + 8*%d], rax \n"  minor)^
                                                          "mov rax, SOB_VOID_ADDRESS \n"
    | ScmSet'(VarFree(name), exp) -> (Printf.sprintf "%s \n" (gen consts fvars exp env_num))^
                                                (Printf.sprintf "mov qword [fvar_tbl+%d], rax \n"  (find_offset_fvar_table fvars name))^
                                                "mov rax, SOB_VOID_ADDRESS \n"
    | ScmBoxGet'(name) -> (Printf.sprintf "%s \n" (gen consts fvars (ScmVar'(name)) env_num))^
                                    "mov rax, qword [rax] \n"
    | ScmBoxSet'(name,exp) -> (Printf.sprintf "%s \n push rax \n %s \n"  (gen consts fvars exp env_num) (gen consts fvars (ScmVar'(name)) env_num))^
                                        "pop qword [rax] \n"^
                                        "mov rax, SOB_VOID_ADDRESS \n"
    | ScmIf' (test, dit, dif) -> gen_if consts fvars test dit dif env_num
    | ScmSeq' (expList) -> List.fold_left(fun asm expr -> asm ^ (gen consts fvars expr env_num) ^ "\n") "" expList
    | ScmOr' (expList) -> gen_or consts fvars expList env_num
    | ScmDef'(var, exp) -> let new_exp = ScmSet'(var,exp) in
                            (Printf.sprintf "%s \n" (gen consts fvars new_exp env_num))
    | ScmBox'(var) -> "MALLOC r8, 8 \n"^
                      (Printf.sprintf "%s \n" (gen consts fvars (ScmVar'(var)) env_num))^
                      "mov qword[r8], rax \n"^
                      "mov rax, r8 \n"
    | ScmLambdaSimple' (vars, body) -> gen_lambda_simple consts fvars vars body env_num
    | ScmLambdaOpt' (vars, varList, body) -> gen_lambda_opt consts fvars vars varList body env_num 
    | ScmApplic'(rator, rands) -> gen_applic consts fvars rator rands env_num
    | ScmApplicTP'(rator, rands) -> gen_applicTP consts fvars rator rands env_num
    
  and gen_or consts fvars expList env_num =
    let label_count  =   get_counter label_counter in
    let rec run_gen_or consts fvars expList env_num label_count = 
      match expList with
      | [] -> ""
      | [exp] -> (gen consts fvars exp env_num) ^ "\n Lexit"^ label_count ^":  \n"
      | exp :: rest -> (gen consts fvars exp env_num) ^ "\n cmp rax, SOB_FALSE_ADDRESS\n jne Lexit"^ label_count ^" \n" ^ (run_gen_or consts fvars rest env_num label_count) in
    run_gen_or consts fvars expList env_num label_count
  
  and gen_if consts fvars test dit dif env_num =
    (* let inc_counter = inc_counter in  *)
    let label_count  =  get_counter label_counter in
    (gen consts fvars test env_num) ^ "\n cmp rax, SOB_FALSE_ADDRESS \n je Lelse"^ label_count ^ "\n "^ 
    (gen consts fvars dit env_num) ^ "jmp Lexit"^ label_count ^ " \n Lelse"^ label_count ^ ":  \n"^ 
    (gen consts fvars dif env_num) ^ "\n Lexit"^ label_count ^ ": \n"
  
  and gen_lambda_simple consts fvars vars body env_num =
    let label_count  = get_counter label_counter  in
    let extaneded_env = extend_env vars env_num label_count in
    let clousre = "MAKE_CLOSURE(rax, rbx, Lcode"^ label_count ^ ") \n jmp Lcont"^ label_count ^ " \n" in
    let body = "Lcode"^ label_count ^ ": \n push rbp \n mov rbp, rsp \n" ^ (gen consts fvars body (env_num + 1)) ^ "leave \n ret\n Lcont"^ label_count ^ ": \n" in
    extaneded_env ^ clousre ^ body

  
  and extend_env vars env_num label_count =
    if env_num = 0
      then "mov rbx, SOB_NIL_ADDRESS ; empty ENV\n"
      else
        (Printf.sprintf "MALLOC rbx, %d ; rbx = new ENV \n" ((env_num ) * 8)) ^
        (copy_pointers (env_num - 1))^
        "mov rcx, qword[rbp + 8 * 3] ; rcx = size of new newEnv[0] \n" ^
        
        "shl rcx, 3 ; rcx * 8 \n"^
        "MALLOC rdx, rcx \n "^

        "mov r8, qword[rbp + 8 * 3] \n"^
        "mov r9, 0 \n"^
        "lea r10, [rbp + 4*8] \n"^

        "Loop"^ label_count ^ ": \n"^



        "cmp r8, 0 \n"^
        "je ExitLoop"^ label_count ^ " \n"^

        "mov rcx, qword[r10] \n"^
        "mov qword[rdx + r9], rcx \n"^
        "add r9, 8 \n"^
        "add r10, 8 \n"^
        "dec r8 \n"^
        "jmp Loop"^ label_count ^ "\n"^

        "ExitLoop"^ label_count ^ ": \n" ^

        "mov qword[rbx], rdx ; update newEnv[0] \n"




        



  and copy_pointers env_num =
    let asm_code =  "mov qword rcx, [rbp + 8 * 2] ; rcx = old env \n" in
    let asm_loop_code = ref "" in
      for i = 0 to env_num do
        asm_loop_code := !asm_loop_code ^ (Printf.sprintf "mov qword rdx, [rcx + %d * 8] ; rdx = old env[i] \n" i) ^
        (Printf.sprintf "mov qword [rbx + %d * 8], rdx ; newEnv [i+1] = oldEnv [i] \n" (i + 1))
      done ;
      
    asm_code ^ !asm_loop_code

  and gen_lambda_opt consts fvars vars varList body env_num =
    let label_count = get_counter label_counter in
    let extaneded_env = extend_env vars env_num label_count in
    let clousre = "MAKE_CLOSURE(rax, rbx, Lcode"^ label_count ^ ") \n jmp Lcont"^ label_count ^ " \n" in
    let body = opt_body consts fvars vars body env_num label_count in
    extaneded_env ^ clousre ^ body 

  and opt_body consts fvars vars body env_num label_count =
    "Lcode"^ label_count ^ ": \n "^
    "mov rax, qword[rsp + 2 * 8] ; rax = num of total params \n"^
    (Printf.sprintf "mov rbx, %d ; rbx= num of min param \n" (List.length vars)) ^
    "cmp rax, rbx \n" ^
    "je EmptyList"^ label_count ^ " \n" ^

    "mov rdx, rax ; rdx = num of total params \n"^
    "shl rdx, 3 \n"^
    "add rdx, 16 \n" ^
    "mov rcx, rdx ; rcx keep the distance to last param \n"^
    "mov r8, qword[rsp + rdx] ; r8 point to last param \n" ^
    "sub rax, rbx ; rax = list size \n" ^
    "mov rbx, SOB_NIL_ADDRESS \n" ^


    "OptLoop"^ label_count ^ ": \n"^
    "cmp rax, 0 \n" ^
    "je DoneOptLoop"^ label_count ^ " \n"^
    "mov r9, rbx \n"^
    "MAKE_PAIR(rbx, r8, r9) ; rbx is the new pair \n"^
    "dec rax \n"^
    "sub rdx, 8 ; rdx point to next param \n"^
    "mov r8, qword[rsp + rdx] ; r8 point to next param \n" ^
    "jmp OptLoop"^ label_count ^ " \n"^
    
    "DoneOptLoop"^ label_count ^ ": \n" ^
    (Printf.sprintf "mov rax, %d \n" (List.length vars))^
    "inc rax ; rax = new n \n"^
    "mov qword[rsp + 2 * 8], rax \n" ^
    "mov qword[rsp + rcx], rbx ; put the list on param[n] \n"^
    "sub rcx, 8 \n" ^

    "MoveStack"^ label_count ^ ": \n"^
    "cmp rdx, 0 \n" ^
    "jl DoneMoveStack"^ label_count ^ " ; jmp if rcx < 0 \n"^
    "mov qword[rsp + rcx], r8 \n" ^
    "sub rcx, 8 \n" ^
    "sub rdx, 8 \n" ^
    "mov r8, qword[rsp + rdx] ; r8 point to next param \n" ^
    "jmp MoveStack"^ label_count ^ " \n"^

    "DoneMoveStack"^ label_count ^ ": \n"^
    "add rcx, 8 \n"^
    "add rsp, rcx ; update rsp \n"^

    (Printf.sprintf "mov qword[rsp + 2 * 8], %d \n" ((List.length vars) + 1))^


    "jmp DoneOptBody"^ label_count ^ " \n"^

    "EmptyList"^ label_count ^ ": \n"^


    "mov rdx, rax ; rdx = num of total params \n"^
    "shl rdx, 3 \n"^
    "add rdx, 16 \n" ^
    "mov rcx, rdx ; rcx keep the distance to last param \n"^
    "mov rbx, SOB_NIL_ADDRESS \n" ^
    "inc rax ; rax = new n \n"^
    "mov qword[rsp + 2 * 8], rax \n" ^

    "AddEmptyListLoop"^ label_count ^ ": \n"^

    "cmp rcx, 0 \n"^
    "jl DoneAddEmptyListLoop"^ label_count ^ "\n"^
    "mov r8, qword[rsp + rcx] ; r8 = last param \n" ^
    "mov qword[rsp + rcx], rbx ; put the list on param[n] \n"^
    "mov rbx, r8 \n"^
    "sub rcx, 8 \n" ^
    "jmp AddEmptyListLoop"^ label_count ^ " \n"^

    "DoneAddEmptyListLoop"^ label_count ^ ": \n"^
    "push rbx \n" ^

    "DoneOptBody"^ label_count ^ ": \n"^
    "push rbp \n mov rbp, rsp \n" ^ 
    (gen consts fvars body (env_num + 1)) ^ 
    "leave \n ret\n Lcont"^ label_count ^ ": \n"

  and gen_applic consts fvars rator rands env =
    let gen_rands = (List.fold_right(fun rand str -> str ^ (gen consts fvars rand env) ^ "\n push rax \n") rands "") in
    let rands_length = (Printf.sprintf "push %d \n" (List.length rands)) in
    let gen_rator = (gen consts fvars rator env)^ "\n" in
    let call_rator = "push qword[rax+1] \n call qword[rax+9] \n" in
    let clean_up = "add rsp, 8*1 \n pop rbx \n shl rbx, 3 \n add rsp, rbx \n" in
    gen_rands^rands_length^gen_rator^call_rator^clean_up


  and gen_applicTP consts fvars rator rands env =
    let label_count  =  get_counter label_counter in
    let gen_rands = (List.fold_right(fun rand str -> str ^ (gen consts fvars rand env) ^ "\n push rax \n") rands "") in
    let rands_length = (Printf.sprintf "push %d \n" (List.length rands)) in
    let gen_rator = (gen consts fvars rator env)^ "\n" in
    let push_env = "push qword[rax+1] \n push qword[rbp +8*1] \n" in
    let overwrite =  "mov r8, [rbp] \n"^ (* this is the very old rbp *)

                      "mov r9, qword[rbp+ 3*8] \n"^
                      "add r9, 3 \n"^
                      "lea r9, [rbp + 8*r9] \n"^ (* this is the address to the first thing after very old rbp *)

                      "mov r10, rbp \n"^
                      "sub r10, 8 \n"^ (* this is the address to the first thing after old rbp *)

                      "mov r11, rsp \n"^
                      "sub r11, 8 \n"^ (* this is to know we done *)

                      "overWrite"^ label_count ^ ": \n"^ (* TODO: complete the unique number *)
                      "mov r12, qword[r10] \n"^
                      "mov qword[r9], r12 \n"^ (* overwrite the value *)
                      "sub r10, 8 \n"^
                      "sub r9, 8 \n"^
                      "cmp r10, r11 \n"^
                      "jne overWrite"^ label_count ^ " \n"^
                      "add r9, 8 \n"^
                      "mov rsp, r9 \n"^
                      "mov rbp, r8 \n" in

        gen_rands^rands_length^gen_rator^push_env^overwrite^"jmp qword[rax+9] \n"



module Code_Gen : CODE_GEN = struct

let make_consts_tbl asts = 
  let known_consts = [ScmVoid; ScmNil; ScmBoolean(false); ScmBoolean(true)] in 
  let consts_list =  List.fold_left(fun list ast -> List.append list (get_const_list ast)) known_consts asts in
  let consts_set = remove_dup consts_list in
  let expended_consts_list = expansion [] consts_set in
  to_consts_tbl expended_consts_list ;;


let make_fvars_tbl asts = 
    to_fvar_table (remove_dup (List.fold_left(fun list ast -> List.append list (get_fvar_list ast)) primitive_names asts)) 0;;


let generate consts fvars e = 
  gen consts fvars e 0 ;;

end;;

