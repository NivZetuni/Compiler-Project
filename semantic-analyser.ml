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


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

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

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
      | ScmConst(e) -> ScmConst'(e)
      | ScmVar(name) -> ScmVar'(tag_lexical_address_for_var name params env)
      | ScmIf(test, dit, dif) -> ScmIf'((run test params env),(run dit params env),(run dif params env))
      | ScmSeq (expList) -> ScmSeq'( List.map (fun exp -> run exp params env) expList)
      | ScmSet (ScmVar(var), value) -> ScmSet'((tag_lexical_address_for_var var params env),(run value params env))
      | ScmDef(ScmVar(name), value) -> ScmDef'((tag_lexical_address_for_var name params env), run value params env)
      | ScmOr (list) -> ScmOr'(List.map (fun exp -> run exp params env) list)
      | ScmLambdaSimple (varsList, bodys) ->  ScmLambdaSimple'((varsList), (run bodys varsList (params :: env)))
      | ScmLambdaOpt (varsList, var, bodys) -> ScmLambdaOpt'(varsList, var, run bodys (List.append varsList (var::[])) (params::env))
      | ScmApplic(op, valsList) -> ScmApplic'( (run op params env), (List.map (fun exp -> run exp params env) valsList) )
      | _ -> raise X_this_should_not_happen
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
      match pe with
      | ScmConst'(e) -> ScmConst'(e)
      | ScmVar'(name) -> ScmVar'(name)
      | ScmIf'(test, dit, dif) -> ScmIf'((run test false),(run dit in_tail),(run dif in_tail))
      | ScmSeq' (expList) ->
                            let (list_without_last, last) = rdc_rac expList in
                            ScmSeq'(List.append (List.map (fun exp -> run exp false) list_without_last) ((run last in_tail)::[]))
      | ScmSet' (var, value) -> ScmSet'(var, (run value false))
      | ScmDef'(var, value) -> ScmDef'(var, (run value false)) 
      | ScmOr' (list) ->
                        let (list_without_last, last) = rdc_rac list in 
                        ScmOr'(List.append (List.map (fun exp -> run exp false) list_without_last) ((run last in_tail)::[]))
      | ScmLambdaSimple' (varsList, bodys) -> ScmLambdaSimple'(varsList,(run bodys true))
      | ScmLambdaOpt' (varsList, var, bodys) -> ScmLambdaOpt'(varsList,var,(run bodys true))
      | ScmApplic'(op, valsList) -> if in_tail then ScmApplicTP'((run op false), (List.map (fun exp -> run exp false) valsList)) else ScmApplic'((run op false), (List.map (fun exp -> run exp false) valsList)) 
      | _ -> raise X_this_should_not_happen
   in 
   run pe false;;

  (* boxing *)

let find_reads name enclosing_lambda expr =
    let rec run name enclosing_lambda expr last_iter =
      match expr with
        (* | ScmConst'(e) -> [] *)
        | ScmVar'(VarParam(varname, minor)) -> if varname = name then (enclosing_lambda::[]) else []
        | ScmVar'(VarBound(varname, major, minor)) -> if varname = name then (enclosing_lambda::[]) else []
        | ScmIf'(test, dit, dif) -> (List.append (List.append (run name enclosing_lambda test last_iter) (run name enclosing_lambda dit last_iter))(run name enclosing_lambda dif last_iter))
        | ScmSeq' (expList) -> List.fold_left List.append [] (List.map (fun exp -> run name enclosing_lambda exp last_iter) expList)
        | ScmSet' (var, value) -> (run name enclosing_lambda value last_iter) 
        | ScmBoxSet'(var, value) -> (run name enclosing_lambda value last_iter)
        | ScmOr' (list) -> List.fold_left List.append [] (List.map (fun exp -> run name enclosing_lambda exp last_iter) list)
        | ScmLambdaSimple' (varsList, bodys) -> if last_iter 
                                                  then (if (List.mem name varsList) 
                                                        then [] 
                                                        else (run name enclosing_lambda bodys last_iter)) 
                                                  else (if (List.mem name varsList) 
                                                        then [] 
                                                        else (run name (ScmLambdaSimple' (varsList, bodys)) bodys true))
                                                        
        | ScmLambdaOpt' (varsList, var, bodys) -> if last_iter then (if (List.mem name (List.append varsList (var::[]))) then [] else (run name enclosing_lambda bodys last_iter)) 
                                                                else (if (List.mem name (List.append varsList (var::[]))) then [] else (run name (ScmLambdaOpt'(varsList, var, bodys)) bodys true))
        | ScmApplic'(op, valsList) -> (List.append (run name enclosing_lambda op last_iter) (List.fold_left List.append [] (List.map (fun exp -> run name enclosing_lambda exp last_iter) valsList)))
        | ScmApplicTP'(op, valsList) -> (List.append (run name enclosing_lambda op last_iter) (List.fold_left List.append [] (List.map (fun exp -> run name enclosing_lambda exp last_iter) valsList)))
        | e -> [] 
    in
    run name enclosing_lambda expr false;;
    
    
    let find_writes name enclosing_lambda expr =
    let rec run name enclosing_lambda expr last_iter =
      match expr with
        (* | ScmConst'(e) -> []
        | ScmVar'(VarParam(varname, minor)) -> []
        | ScmVar'(VarBound(varname, major, minor)) -> [] *)
        | ScmIf'(test, dit, dif) -> (List.append (List.append (run name enclosing_lambda test last_iter) (run name enclosing_lambda dit last_iter))(run name enclosing_lambda dif last_iter))
        | ScmSeq' (expList) -> List.fold_left List.append [] (List.map (fun exp -> run name enclosing_lambda exp last_iter) expList)
        | ScmSet'(VarParam(varname, minor), value) -> if varname = name then (List.append (enclosing_lambda::[]) (run name enclosing_lambda value last_iter)) else (run name enclosing_lambda value last_iter)
        | ScmSet'(VarBound(varname, major, minor), value) -> if varname = name then (List.append (enclosing_lambda::[]) (run name enclosing_lambda value last_iter)) else (run name enclosing_lambda value last_iter)
        | ScmBoxSet'(var, value) -> (run name enclosing_lambda value last_iter)
        | ScmOr' (list) -> List.fold_left List.append [] (List.map (fun exp -> run name enclosing_lambda exp last_iter) list)
        | ScmLambdaSimple' (varsList, bodys) -> if last_iter 
                                                  then (if (List.mem name varsList) 
                                                          then [] 
                                                          else (run name enclosing_lambda bodys last_iter)) 
                                                  else (if (List.mem name varsList) 
                                                          then [] 
                                                          else (run name (ScmLambdaSimple'(varsList, bodys)) bodys true))
        | ScmLambdaOpt' (varsList, var, bodys) -> if last_iter 
                                                    then (if (List.mem name (List.append varsList (var::[]))) 
                                                            then [] 
                                                            else (run name enclosing_lambda bodys last_iter)) 
                                                    else (if (List.mem name (List.append varsList (var::[]))) 
                                                            then [] 
                                                            else (run name (ScmLambdaOpt'(varsList,var, bodys)) bodys true))
        | ScmApplic'(op, valsList) -> (List.append (run name enclosing_lambda op last_iter) (List.fold_left List.append [] (List.map (fun exp -> run name enclosing_lambda exp last_iter) valsList)))
        | ScmApplicTP'(op, valsList) -> (List.append (run name enclosing_lambda op last_iter) (List.fold_left List.append [] (List.map (fun exp -> run name enclosing_lambda exp last_iter) valsList)))
        | e -> []
    in
    run name enclosing_lambda expr false;;

  let rec box name expr = 
    match expr with
    | ScmVar'(VarParam(varName, minor)) -> if name = varName then ScmBoxGet'(VarParam(varName, minor)) else ScmVar'(VarParam(varName, minor))
    | ScmVar'(VarBound(varName, major, minor)) -> if name = varName then ScmBoxGet'(VarBound(varName, major,minor)) else ScmVar'(VarBound(varName, major,minor)) 
    | ScmBoxSet'(var , value) -> ScmBoxSet'(var , box name value)
    | ScmIf'(test, dit, dif) -> ScmIf'(box name test, box name dit, box name dif)
    | ScmSeq' (expList) -> ScmSeq'( List.map (fun exp -> box name exp) expList)
    | ScmSet' (VarParam(varName, minor), value) -> if varName = name then ScmBoxSet'( (VarParam(varName, minor)),box name value) else ScmSet' (VarParam(varName, minor), box name value)
    | ScmSet' (VarBound(varName, major, minor), value) -> if varName = name then ScmBoxSet'( (VarBound(varName, major, minor)),box name value) else ScmSet' (VarBound(varName, major, minor), box name value)
    | ScmSet' (VarFree(varName), value) ->  ScmSet' (VarFree(varName), box name value)
    | ScmDef'(var, value) -> ScmDef'(var, box name value)
    | ScmOr' (list) -> ScmOr'(List.map (fun exp -> box name exp) list)
    | ScmLambdaSimple' (varsList, bodys) -> if List.mem name varsList
                        then ScmLambdaSimple' (varsList, bodys)
                        else ScmLambdaSimple' (varsList, box name bodys)
    | ScmLambdaOpt' (varsList, var, bodys) -> if List.mem name varsList
                        then ScmLambdaOpt' (varsList, var, bodys)
                        else if name = var
                              then ScmLambdaOpt' (varsList, var, bodys)
                              else ScmLambdaOpt' (varsList, var, box name bodys)
    | ScmApplic'(op, valsList) -> ScmApplic'(box name op , (List.map (fun exp -> box name exp) valsList) )
    | ScmApplicTP'(op, valsList) -> ScmApplicTP'(box name op , (List.map (fun exp -> box name exp) valsList) )
    | expr' -> expr' 

  let change_body body var minor =
    match body with
    | ScmSeq'(oldBody) -> ScmSeq'(List.append [(ScmSet'(VarParam(var, minor), ScmBox'(VarParam(var,minor))))] (List.map (fun body -> box var body) oldBody))
    | oldBody -> ScmSeq'(List.append [(ScmSet'(VarParam(var, minor), ScmBox'(VarParam(var,minor))))] [(box var oldBody)])

  let is_box_needed name enclosing_lambda body =
    let readList = find_reads name enclosing_lambda body in
    let writeList = find_writes name enclosing_lambda body in
    (* let (read, last) = rdc_rac readList in *)
    (* let (write, last2) = rdc_rac writeList in

    let sds = (expr'_eq last last2)in
    false *)
    if (List.length readList) = 0 
      then false
      else if (List.length writeList) = 0 
              then false
              else List.fold_left (fun b a -> b || a ) false (List.map (
                      fun read -> List.fold_left (fun b a -> b || a ) false (List.map (
                        fun write -> not (read = write)
                      ) writeList)
                    ) readList)
    

let rec box_on_lambda_vars vars body enclosing_lambda =
    match vars with
    | [] -> body
    | head::tail -> let (vars_without_last, last) = rdc_rac vars in
                                if (is_box_needed last enclosing_lambda body)
                                then (box_on_lambda_vars vars_without_last (change_body body last ((List.length vars) - 1)) enclosing_lambda) 
                                else (box_on_lambda_vars vars_without_last body enclosing_lambda)

let rec box_set expr = 
    match expr with
    | ScmIf'(test, dit, dif) -> ScmIf'(box_set test, box_set dit, box_set dif)
    | ScmSeq' (expList) -> ScmSeq'( List.map (fun exp -> box_set exp) expList)
    | ScmSet' (var, value) -> ScmSet'( var,box_set value)
    | ScmBoxSet' (var, value) -> ScmBoxSet'( var,box_set value)
    | ScmDef'(var, value) -> ScmDef'(var, box_set value)
    | ScmOr' (list) -> ScmOr'(List.map (fun exp -> box_set exp) list)
    | ScmLambdaSimple' (varsList, bodys) ->  ScmLambdaSimple'((varsList), (box_set (box_on_lambda_vars varsList bodys (ScmLambdaSimple'(varsList, bodys)))))
    | ScmLambdaOpt' (varsList, var, bodys) -> ScmLambdaOpt'(varsList, var, (box_set (box_on_lambda_vars (List.append varsList (var::[])) bodys (ScmLambdaOpt'(varsList,var, bodys)))))
    | ScmApplic'(op, valsList) -> ScmApplic'(box_set op , (List.map (fun exp -> box_set exp) valsList) )
    | ScmApplicTP'(op, valsList) -> ScmApplicTP'(box_set op , (List.map (fun exp -> box_set exp) valsList) )
    | expr' -> expr';;
  


  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
