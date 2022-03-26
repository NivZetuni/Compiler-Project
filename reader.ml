(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;
  
let rec makeNotNormal f =
  if f < 1.0 then f else
    makeNotNormal (f /. 10.0);;

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
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str
(* ; *)
and nt_line_comment str = 
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
  let nt1 = unitify nt1 in
  nt1 str
(* { } *)
and nt_paired_comment str = 
  let nt_start = char '{' in
  let nt_end = char '}' in
  let nt_stringquote = char '\"' in
  let nt_innerstring = star (diff nt_any nt_stringquote)in
  let nt_innerstring = unitify (caten nt_stringquote (caten nt_innerstring nt_stringquote))in
  let nt_str = disj nt_paired_comment (disj (unitify (disj (word "#\\}") (word "#\\{"))) (disj nt_innerstring (unitify (diff nt_any nt_end) ))) in
  let nt1 = star nt_str in
  let nt1 = caten nt_start (caten nt1 nt_end) in
  let nt1 = unitify nt1 in 
  nt1 str
(* #; *)
(* and nt_sexpr_comment str = 
    let nt1 = word "#;" in
    let nt_quote = char '\"' in
    let nt_open = char '(' in
    let nt_close = char ')' in
    let nt_quoteafter = star nt_whitespace in
    let nt_str = diff nt_any nt_quote in
    let nt_str = star nt_str in
    let nt_space = word " "in
    let nt_spaces = star nt_space in
    let nt_word = diff nt_any (disj nt1 nt_space)in
    let nt_word = plus nt_word in
    let nt_word = unitify nt_word in
    let nt_str = caten nt_quote (caten nt_str (caten nt_quote nt_quoteafter)) in
    let nt_lis = diff nt_any nt_close in
    let nt_lis = star nt_lis in
    let nt_lis = caten nt_open (caten nt_lis (caten nt_close nt_quoteafter)) in
    let nt_str = disj nt_str nt_lis in
    let nt_str = unitify nt_str in
    let nt_str = disj nt_str nt_word in
    let nt_str = caten nt_spaces nt_str in
    let nt_again = star nt_sexpr_comment in
    let nt = caten nt1 (caten nt_again nt_str) in
    let nt = unitify nt in
    nt str *)
    and nt_sexpr_comment str = 
    let nt1 = word "#;" in

    let nt_str = nt_sexpr in
    let nt_again = star nt_sexpr_comment in
    let nt = caten nt1 (caten nt_again nt_str) in
    let nt = unitify nt in
    nt str
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
and nt_natural str=
  let nt1 = range '0' '9' in
  let nt1 = pack nt1 
                  (let delta = int_of_char '0' in
                  fun ch -> (int_of_char ch) - delta)in
  let nt1 = plus nt1 in
  let nt1 = pack nt1 (fun digits -> List.fold_left(fun a b -> 10 * a + b) 0 digits) in
  nt1 str
and nt_int str = 
  let nt_positive = char '+' in
  let nt_negative = char '-' in
  let nt2 = disj nt_positive nt_negative in
  let nt2 = maybe nt2 in
  let nt1 = caten nt2 nt_natural in 
  let nt1 = pack nt1
                (fun (s, n) -> match s with
                        |  Some ('-') -> -n
                        | _ -> n
                ) in
  nt1 str
and nt_frac str = 
  let nt1 = char '/' in
  let nt1 = caten nt_int nt1 in
  let nt0 = only_if nt_natural (fun i -> i != 0) in
  let nt1 = caten nt1 nt0 in
  let nt1 = pack nt1 (
                      fun ((a, b), c) -> ScmRational(a/(gcd (a) (c)), c/(gcd (a) (c))) 
                                        ) in
  nt1 str
and nt_integer_part str = 
  let nt1 = nt_natural in
  nt1 str
and nt_mantissa str = 
  let nt = nt_natural in
  nt str
and nt_exponent str = 
  let nt_exponent1 = word_ci "e" in
  let nt_exponent2 = word "*10^" in
  let nt_exponent3 = word "*10**" in
  let nt_exps = disj nt_exponent1 (disj nt_exponent2 nt_exponent3) in
  let nt1 = caten nt_exps nt_int in
  let nt1 = pack nt1 (fun (e, n) -> 10.0**(float)n ) in
  nt1 str
and nt_floatA str =
  let nt1 = nt_integer_part in
  let nt2 = char '.' in
  let nt3 = nt_mantissa in
  let nt4 = nt_exponent in
  let nt1 = caten nt1 (caten nt2 (caten (maybe nt3) (maybe nt4))) in
  let nt1 = pack nt1 (fun (i, (d, me)) -> match me with
                                          | (Some(m), Some(e)) -> (((float) i) +. (makeNotNormal (float m)))*. e
                                          | (Some(m), _) -> (((float) i) +. (makeNotNormal (float m)))
                                          | ( _ , Some(e)) -> (((float) i) *. e)
                                          | _ -> (float i)
                                          ) in
  nt1 str
and nt_floatB str =
  let nt1 = char '.' in
  let nt2 = nt_mantissa in
  let nt3 = maybe nt_exponent in
  let nt1 = caten nt1 (caten nt2 nt3) in
  let nt1 = pack nt1 (fun (p, (m, e)) -> match e with
                                        | Some(b) -> ((makeNotNormal ((float)m)))*.b
                                        | _ -> (makeNotNormal ((float)m))
                                        )in
  nt1 str
and nt_floatC str =
  let nt1 = caten nt_integer_part nt_exponent in
  let nt1 = pack nt1 (fun (i, e)-> ((float)i)*.e) in
  nt1 str
and nt_float str = 
  let nt1 = disj nt_floatA (disj nt_floatB nt_floatC) in
  let nt2 = char '-' in
  let nt3 = char '+' in
  let nt2 = disj nt2 nt3 in
  let nt2 = maybe nt2 in
  (* let nt2 = unitify nt2 in *)
  let nt1 = caten  nt2 nt1 in
  let nt1 = pack nt1 (fun (s, n) -> match s with
                                  | Some('-') ->ScmReal( -.n)
                                  | _ ->ScmReal( n)
                                  ) in
  nt1 str
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
  let nt1 = pack nt1 (fun _-> false)in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _-> true)in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  nt1 str
and nt_char_simple str = 
  let nt1 = const (fun (c) -> ' ' < c ) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
and make_named_char char_name ch = 
  pack (word_ci char_name) (fun _ -> ch)
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "nul" '\000');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str = 
        let digit = range '0' '9' in
        let letter = range_ci 'a' 'f' in
        let nt1 = disj letter  digit in
        let nt1 = pack nt1 (fun (c) -> lowercase_ascii c ) in
        nt1 str
and nt_hexadecimal_char str =
  let ntx = char_ci 'x' in
  let ntn = pack nt_char_hex 
                (let deltan = int_of_char '0' in
                let deltal = 87 in
                fun ch -> if ch <= '9' then (int_of_char ch) - deltan else (int_of_char ch) - deltal)in
  let ntn = plus ntn in 
  let ntn = pack ntn (fun digits -> List.fold_left(fun a b -> 16 * a + b) 0 digits) in
  let ntn = only_if ntn (fun i -> i <= 256)in
  let nt = caten ntx ntn in
  let nt = pack nt (fun (x, n) -> char_of_int n) in
  nt str
and nt_char_prefix str = 
  let nt1 = word_ci "#\\" in
  let nt1 = pack nt1 (fun c -> list_to_string c) in
  nt1 str
and nt_char str = 
  let nt1 = caten nt_char_prefix (disj nt_char_named (disj nt_char_simple nt_hexadecimal_char)) in
  let nt1 = pack nt1 (fun (pref, c) -> ScmChar c) in
  nt1 str
and nt_symbol_char str = 
    let digit = range '0' ':' in
    let lowerletter = range 'a' 'z' in
    let upperletter = range 'A' 'Z' in
    let other = disj (disj (disj (disj (char '!') (char '$')) (char '/')) (char ':')) (char '-')  in
    let other2 = disj (disj (range '<' '?') (range '*' '+')) (range '^' '_')  in
    let nt1 = disj (disj (disj (disj lowerletter upperletter) other) other2) digit in
    nt1 str
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str
and nt_quote_backslash_tilde str =
  let nt1 = unitify (char '\"') in
  let nt2 = unitify (char '\\') in
  let nt3 = unitify (char '~') in
  let nt1 = disj nt1 (disj nt2 nt3) in
  nt1 str
and nt_string_literal_char str =
  let nt1 = diff nt_any nt_quote_backslash_tilde in
  nt1 str
and nt_string_meta_char str =
  let nt1 = char_ci '\\' in
  let nt2 = char_ci '"' in
  let nt3 = char_ci 't' in
  let nt4 = char_ci 'f' in
  let nt5 = char_ci 'n' in
  let nt6 = char_ci 'r' in
  let nt7 = char '~' in
  let ntb = disj_list [
              nt1;
              nt2;
              nt3;
              nt4;
              nt5;
              nt6] in
  let ntb = caten nt1 ntb in
  let ntb = pack ntb (fun (b, c) -> match c with
                            | '\\' -> (char_of_int 92)
                            | '"' -> '"'
                            | 't' -> '\t'
                            | 'f' -> '\012'
                            | 'n' -> '\n'
                            | 'r' -> '\r'
                            | x ->  x
                            )in
  let ntt = caten nt7 nt7 in
  let ntt = pack ntt (fun (t1, t2) -> match t2 with
                                    | '~' -> '~'
                                    | x -> x
                                    )in
  let nt = disj ntb ntt in
  nt str
and nt_string_hex_char str =
  let ntend = char ';' in
  let ntx = word_ci "\\x" in
  let ntn = pack nt_char_hex 
                  (let deltan = int_of_char '0' in
                  let deltal = 87 in
                  fun ch -> if ch <= '9' then (int_of_char ch) - deltan else (int_of_char ch) - deltal)in
  let ntn = plus ntn in 
  let ntn = pack ntn (fun digits -> List.fold_left(fun a b -> 16 * a + b) 0 digits) in
  let nt = caten ntx (caten ntn ntend) in
  let nt = pack nt (fun (x, (n, e)) -> char_of_int n)in
  nt str
and nt_string_char str =
  let nt1 = disj_list [
              nt_string_literal_char;
              nt_string_meta_char;
              nt_string_hex_char] in
  nt1 str
and nt_string_interpolated str =
  let nt1 = word "~{" in
  let nt2 = char '}' in
  let nts = nt_sexpr in
  let nt = caten nt1 (caten nts nt2) in
  let nt = pack nt (fun (_, (s, _)) -> ScmPair(ScmSymbol("format") ,ScmPair(ScmString("~a"), ScmPair(s, ScmNil))))in
  nt str
and nt_string str = 
  let nt_quote = char '\"' in
  let nt_str = plus nt_string_char in
  let nt_str = pack nt_str (fun s ->  ScmString(list_to_string s)) in
  let nt_str = star (disj nt_str nt_string_interpolated) in
  let nt = caten nt_quote (caten nt_str nt_quote) in
  let nt = pack nt (fun (l, (s, r)) ->  if ((List.length s) == 1) then List.fold_left(fun a b -> b) ScmNil s 
                                            else if ((List.length s) == 0) then ScmString("") 
                                              else ScmPair(ScmSymbol("string-append"), List.fold_right(fun a b -> ScmPair(a, b)) s ScmNil)) in
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
and nt_proper_list str =
  let nt1 = char '(' in
  let nt2 = char ')' in
  let nt4 = caten nt_skip_star nt2 in
  let nt4 = pack nt4 (fun _ -> ScmNil) in 
  let nt3 = caten( star nt_sexpr) nt2 in
  let nt3 = pack nt3 (fun (sexprs, _) -> List.fold_right(fun a b -> ScmPair(a, b)) sexprs ScmNil) in
  let nt3 =  disj nt3 nt4  in
  let nt1 = caten nt1 nt3 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str
and nt_improper_list str =
  let nt1 = char '(' in
  let nt2 = char ')' in
  let nt3 = nt_sexpr in
  let nt4 = char '.' in
  let nt4 = caten nt_skip_star nt4 in
  let nt4 = pack nt4 (fun (_, d) -> d) in
  let nt5 = plus nt_sexpr in
  let nt5 = caten nt5 (caten nt4 nt3) in
  let nt5 = pack nt5 (fun (sexprs, (d, sexpr)) -> List.fold_right(fun a b -> ScmPair(a, b)) sexprs sexpr) in
  let nt = caten nt1 (caten nt5 nt2) in
  let nt = pack nt (fun (_, (sexpr, _)) -> sexpr)in
  nt str
and nt_list str =
  let nt = disj nt_proper_list nt_improper_list in
  nt str
and nt_quoted str =
  let nt1 = char '\'' in
  let nt1 = pack nt1 (fun _ -> ScmSymbol("quote")) in
  let nt2 = nt_sexpr in
  let nt2 = pack nt2 (fun sexpr -> ScmPair(sexpr, ScmNil)) in
  let nt = caten nt1 nt2 in
  let nt = pack nt (fun (symbol, pair) -> ScmPair(symbol, pair))in
  nt str
and nt_quasi_quoted str =
  let nt1 = char '`' in
  let nt1 = pack nt1 (fun _ -> ScmSymbol("quasiquote")) in
  let nt2 = nt_sexpr in
  let nt2 = pack nt2 (fun sexpr -> ScmPair(sexpr, ScmNil)) in
  let nt = caten nt1 nt2 in
  let nt = pack nt (fun (symbol, pair) -> ScmPair(symbol, pair))in
  nt str
and nt_unquoted str =
  let nt1 = char ',' in
  let nt1 = pack nt1 (fun _ -> ScmSymbol("unquote")) in
  let nt2 = nt_sexpr in
  let nt2 = pack nt2 (fun sexpr -> ScmPair(sexpr, ScmNil)) in
  let nt = caten nt1 nt2 in
  let nt = pack nt (fun (symbol, pair) -> ScmPair(symbol, pair))in
  nt str
and nt_unquoted_splicing str =
  let nt1 = word ",@" in
  let nt1 = pack nt1 (fun _ -> ScmSymbol("unquote-splicing")) in
  let nt2 = nt_sexpr in
  let nt2 = pack nt2 (fun sexpr -> ScmPair(sexpr, ScmNil)) in
  let nt = caten nt1 nt2 in
  let nt = pack nt (fun (symbol, pair) -> ScmPair(symbol, pair)) in
  nt str
and nt_quoted_forms str = 
  let nt = disj_list [nt_quoted; nt_quasi_quoted; nt_unquoted; nt_unquoted_splicing] in
  nt str
and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str

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
