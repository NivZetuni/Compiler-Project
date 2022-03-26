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

let macro_word_list =
  ["and"; "cond"; "let"; "let*"; "letrec"; "quasiquote"];;
    

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
| ScmNil -> (ScmConst ScmNil)
| ScmBoolean(b) -> ScmConst(ScmBoolean(b))
| ScmChar(c) -> ScmConst(ScmChar(c))
| ScmNumber(n) -> ScmConst(ScmNumber(n))
| ScmString(s) -> ScmConst(ScmString(s))
| ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil)) -> ScmConst(x)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmNil))) -> ScmIf(tag_parse_expression test, tag_parse_expression dit, ScmConst ScmVoid)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))) -> ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
| ScmPair(ScmSymbol "or", ScmNil) -> ScmConst (ScmBoolean false)
| ScmPair(ScmSymbol "or", ScmPair (sexp, ScmNil)) -> tag_parse_expression sexp
| ScmPair(ScmSymbol "or", list) -> ScmOr (scm_list_to_expr_list list)
| ScmPair(ScmSymbol "lambda", pair) -> lambda_cases pair
| ScmPair(ScmSymbol "define", ScmPair (ScmSymbol (var), ScmPair(value, ScmNil))) -> if not(List.mem var reserved_word_list) then ScmDef(ScmVar var, tag_parse_expression value) else raise (X_syntax_error (sexpr, "Expected variable on LHS of define"))
| ScmPair(ScmSymbol "define", ScmPair(ScmPair (ScmSymbol var, args), body)) -> if not(List.mem var reserved_word_list) then ScmDef(ScmVar var, tag_parse_expression (ScmPair(ScmSymbol "lambda",ScmPair(args, body)))) else raise (X_syntax_error (sexpr, "Expected variable on LHS of define"))
| ScmPair(ScmSymbol "set!", pair) -> scm_set_pair pair
| ScmPair(ScmSymbol "begin", ScmNil) -> tag_parse_expression ScmNil
| ScmPair(ScmSymbol "begin", ScmPair(sexp, rest)) -> if scm_list_length (ScmPair(sexp, rest)) = 1 then tag_parse_expression sexp else ScmSeq (scm_list_to_expr_list (ScmPair(sexp, rest)))
| ScmPair(op, appliction) -> ScmApplic((tag_parse_expression op), (scm_list_to_expr_list appliction))
| ScmSymbol(var) -> if not(List.mem var reserved_word_list) then ScmVar var else raise (X_reserved_word (var ^ " is reserved word"))
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and macro_expand sexpr =
match sexpr with
| ScmPair (ScmSymbol "and", ScmNil) -> ScmBoolean(true)
| ScmPair (ScmSymbol "and", ScmPair(hd,  ScmNil)) ->  hd
| ScmPair (ScmSymbol "and", ScmPair(hd, tl)) -> if not(sexpr_eq tl ScmNil) then ScmPair(ScmSymbol("if"), ScmPair(hd, ScmPair( macro_expand (ScmPair(ScmSymbol ("and"),tl)), ScmPair(ScmBoolean(false), ScmNil)))) else  tl
| ScmPair (ScmSymbol "let", ScmPair (vars, bodys)) -> ScmPair (ScmPair(ScmSymbol "lambda", ScmPair(get_vars vars, bodys)), get_values vars)
| ScmPair (ScmSymbol "let*", ScmPair (vars, bodys)) -> le_t_star_cases (ScmPair(vars, bodys))
| ScmPair (ScmSymbol "letrec",ScmPair (ScmNil, bodys)) -> macro_expand (ScmPair (ScmSymbol "let", ScmPair (ScmNil, body_for_letrec_nil bodys)))
| ScmPair (ScmSymbol "letrec",ScmPair (vars, bodys)) -> macro_expand (ScmPair (ScmSymbol "let", ScmPair (vars_for_letrec vars, body_for_letrec (vars, bodys))))
| ScmPair (ScmSymbol "cond",ribs) -> cond_ribs_cases ribs
| ScmPair (ScmSymbol "quasiquote",ScmPair(rest, ScmNil)) -> qq_cases rest

| _ -> sexpr

and qq_cases = function
| ScmPair(ScmSymbol("unquote"), ScmPair(x, ScmNil)) -> x
| ScmPair(ScmSymbol("unquote-splicing"), rest) -> ScmPair(ScmSymbol("quote"),ScmPair(ScmPair(ScmSymbol("unquote-splicing"), rest), ScmNil))
| ScmNil -> ScmPair(ScmSymbol("quote"), ScmPair(ScmNil, ScmNil))
| ScmSymbol(x) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol(x), ScmNil))
| ScmVector vec -> ScmPair(ScmSymbol "list->vector", ScmPair((qq_cases (list_to_proper_list vec), ScmNil)))
| ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(rest, ScmNil)), tl) -> ScmPair(ScmSymbol "append", ScmPair (rest, ScmPair(( qq_cases tl), ScmNil)))
| ScmPair(hd, tl) -> ScmPair(ScmSymbol "cons",ScmPair(qq_cases hd, ScmPair (( qq_cases tl),ScmNil)))
| sexpr -> sexpr


and body_for_letrec_nil = function
| ScmPair(bodys, ScmNil) -> ScmPair(bodys, ScmNil)
| sexpr -> raise (X_syntax_error (sexpr, "couldnt make body for letrec nil"))


and body_for_letrec = function
| (ScmNil, bodys) -> bodys
| (ScmPair (ScmPair (var1, val1), vars), bodys) -> ScmPair (ScmPair (ScmSymbol "set!", ScmPair (var1, val1)), body_for_letrec (vars, bodys))
| (sexpr, sexpr2) -> raise (X_syntax_error (ScmPair(sexpr, sexpr2), "couldnt make body for letrec "))

and vars_for_letrec = function
| ScmNil -> ScmNil
| ScmPair (ScmPair (var1,_), vars) -> ScmPair (ScmPair (var1, ScmPair (ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol "whatever", ScmNil)), ScmNil)), vars_for_letrec vars)
| sexpr -> raise (X_syntax_error (sexpr, "couldnt make vars for letrec "))


and cond_ribs_cases = function
| ScmPair(ScmPair(ScmSymbol "else", ScmPair(rest, ScmNil)), _) -> rest
| ScmPair(ScmPair(ScmSymbol "else", rest), _) -> ScmPair(ScmSymbol "begin", rest)

| ScmPair(ScmPair(test, ScmPair(ScmSymbol "=>", ScmPair (func, ScmNil))), dif) -> macro_expand (ScmPair (ScmSymbol "let", ScmPair(
      ScmPair(ScmPair(ScmSymbol "value" , ScmPair(test, ScmNil)), 
      ScmPair(ScmPair(ScmSymbol "f" ,  ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil , ScmPair( func, ScmNil))), ScmNil)) , 
      ScmPair(ScmPair(ScmSymbol "rest", ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil , ScmPair( cond_ribs_cases dif, ScmNil))), ScmNil)), ScmNil))),
  ScmPair(ScmPair(ScmSymbol "if", ScmPair(ScmSymbol "value", 
  ScmPair(ScmPair(ScmPair(ScmSymbol "f", ScmNil), ScmPair(ScmSymbol "value", ScmNil)),
  ScmPair( ScmPair(ScmSymbol "rest" ,ScmNil), ScmNil)))), ScmNil))))


| ScmPair(ScmPair(test, ScmPair (dit, ScmNil)), ScmNil) -> ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmNil)))
| ScmPair(ScmPair(test, dit), ScmNil) -> ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol "begin", dit), ScmNil)))
| ScmPair(ScmPair(test, ScmPair (dit, ScmNil)), rest) -> ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(cond_ribs_cases rest, ScmNil))))
| ScmPair(ScmPair(test, dit), rest) -> ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol "begin", dit), ScmPair(cond_ribs_cases rest, ScmNil))))
| sexpr -> raise (X_syntax_error (sexpr, "couldnt make cond ribs "))

and le_t_star_cases = function
| ScmPair (ScmNil, ScmPair(bodys, ScmNil)) -> macro_expand (ScmPair(ScmSymbol "let", ScmPair (ScmNil, ScmPair(bodys, ScmNil))))
| ScmPair (ScmPair(vr1, ScmNil), bodys) -> macro_expand (ScmPair (ScmSymbol "let", ScmPair(ScmPair(vr1, ScmNil), bodys)))
| ScmPair (ScmPair(vr1, vrs), bodys) -> macro_expand (ScmPair (ScmSymbol "let",ScmPair(ScmPair(vr1, ScmNil), ScmPair( macro_expand (ScmPair (ScmSymbol "let*", ScmPair (vrs, bodys))), ScmNil))))
| sexpr -> raise (X_syntax_error (sexpr, "couldnt make let* "))
and get_vars = function
| ScmPair(ScmPair(vr, _), tl) -> ScmPair(vr, get_vars tl)
| ScmNil -> ScmNil
| sexpr -> raise (X_syntax_error (sexpr, " in let macro expansion var not in the correct struct"))

and get_values = function
| ScmPair(ScmPair(_, ScmPair(value, ScmNil)), tl) -> ScmPair(value, get_values tl)
| ScmNil -> ScmNil
| sexpr -> raise (X_syntax_error (sexpr, " in let macro expansion values not in the correct struct"))

and scm_set_pair = function
| ScmPair (ScmSymbol var, ScmPair (value, ScmNil)) -> ScmSet(ScmVar var, tag_parse_expression value)
| sexpr -> raise (X_syntax_error (sexpr, "Expected variable on LHS of set!"))

and scm_list_to_expr_list = function
| ScmPair (hd, tl) -> tag_parse_expression hd::(scm_list_to_expr_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list (list to expr)"))

and scm_list_to_string_list = function
| ScmPair (ScmSymbol(hd), tl) -> hd::(scm_list_to_string_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list (list to string list)"))

and scm_is_any_list = function
| ScmNil -> true
| ScmPair (_) -> true
| _ -> false

and scm_is_proper_list = function
| ScmPair (hd, tl) -> (scm_is_proper_list tl)
| ScmNil -> true
| _ -> false

and get_last = function
| ScmPair (hd, tl) -> (get_last tl)
| ScmSymbol(x) -> x
| sexpr -> raise (X_syntax_error (sexpr, "Expected pair or symbol"))

and remove_last = function
| ScmPair (hd, tl) -> ScmPair(hd, (remove_last tl))
| ScmSymbol(_) -> ScmNil
| sexpr -> raise (X_syntax_error (sexpr, "Expected pair or symbol"))


and lambda_cases = function
| ScmPair(ScmNil, ScmPair(body, ScmNil)) -> ScmLambdaSimple([], tag_parse_expression body)
| ScmPair(vars, body) -> if scm_is_any_list vars then (if scm_is_proper_list vars then args_are_proper_list (ScmPair(vars, body)) else args_are_improper_list (ScmPair(vars, body))) else arg_is_list (ScmPair(vars, body))
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper lambda"))

and args_are_proper_list = function
| ScmPair(vars, ScmPair (body, ScmNil)) -> ScmLambdaSimple((scm_list_to_string_list vars), tag_parse_expression body)
| ScmPair(vars, ScmPair (hd, tl)) -> ScmLambdaSimple((scm_list_to_string_list vars), ScmSeq (scm_list_to_expr_list (ScmPair(hd, tl))))
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list args"))

and args_are_improper_list = function
| ScmPair(vars, ScmPair (body, ScmNil)) -> ScmLambdaOpt((scm_list_to_string_list (remove_last vars)), get_last vars, tag_parse_expression body)
| ScmPair(vars, ScmPair (body, rest)) -> ScmLambdaOpt((scm_list_to_string_list (remove_last vars)), get_last vars, ScmSeq (scm_list_to_expr_list (ScmPair (body, rest)) ))
| sexpr -> raise (X_syntax_error (sexpr, "Expected improper list args"))

and arg_is_list = function
| ScmPair(ScmSymbol(vars), ScmPair (body, ScmNil)) -> ScmLambdaOpt([], vars, tag_parse_expression body)
| ScmPair(ScmSymbol(vars), ScmPair (body, rest)) -> ScmLambdaOpt([], vars, ScmSeq (scm_list_to_expr_list (ScmPair (body, rest))))
| sexpr -> raise (X_syntax_error (sexpr, "Expected list arg"))
end;; 

