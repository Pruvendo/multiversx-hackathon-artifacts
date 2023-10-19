Require Import String.
Require Import List. 
Require Import Bool. 
Require Import CoqJson.Json.
Require Import CoqJson.KeyMaps.
Require Import Ascii.
Require Import UtilityFunctions.
Require Import Notations.
Import ListNotations.
Import BoolNotations. 
Open Scope string_scope.

(* REMOVE *)
Notation "b '-->' something '!'  " := (getString(json_get(inl something )(b))) (at level 500, left associativity).
Notation "b '-->' something '?'  " := (getJSON(json_get(inl something )(b))) (at level 500, left associativity).
Notation "b '-->' something '??'  " := ((json_get(inl something )(b))) (at level 500, left associativity).
Notation "'\n' a" := (String "010"%char a)(at level 0).

Inductive rValue: Set := 
| rIdent (name: string): rValue
| rLiteral (literal: string) (kind:string) (subdenomination: string): rValue
| rReferenceMod (type: rValue)
| rSliceMod (type: rValue)
| rTypeIdent (type: string): rValue
| rBinOperation (operation: string) (left right: rValue): rValue
| rUnOperation (is_infix: bool) (operation: string) (object: rValue): rValue
| rField (object: rValue) (member: string): rValue
| rIndex (object: rValue) (index: rValue): rValue
| rTuple (objects: list rValue): rValue
| rFunCall (callable_object: rValue) (args: list rValue) (kind: string): rValue
| rError (error_string: string): rValue
| rCond (cond true_val false_val: rValue)
| rLambda (args: list (rValue)) (returns: rValue)(body: rValue)
.

Inductive lValue: Set := 
| lField (object: lValue) (member: string): lValue
| lIndex (object: lValue) (index: rValue): lValue
| lTuple (objects: list lValue): lValue
| lFunCall (callable_object: lValue) (args: list rValue): lValue
| lUnOperation (is_infix: bool) (operation: string) (object: lValue): lValue
| lIdent (name: string): lValue
| lError (error_string: string): lValue
.

Inductive UrsusStatement: Set := 
| UBlock (block: list UrsusStatement)
| UIf_Then_Else (cond: rValue) (true_body: UrsusStatement) (false_body: UrsusStatement) (cond_lice: bool) (lice_then: bool) (lice_else: bool)
| UIf_Then (cond: rValue) (true_body: UrsusStatement) (cond_lice: bool) (lice_then: bool)
| UDefaultVarDeclaration (object: list (lValue * rValue)): UrsusStatement
| UVarDeclaration (object: list (lValue * rValue)) (value: rValue): UrsusStatement
| UAssignment (operator: string) (left: lValue) (right: rValue) : UrsusStatement
| UForeach_loop (range_declaration: list string) (range_expression: rValue) (body: UrsusStatement) (lice:bool)
| UFor_loop (condition: rValue) (initialization_expression: UrsusStatement) (loop_expression: UrsusStatement) (body: UrsusStatement) (lice:bool)
| UWhile_loop (condition: rValue) (body: UrsusStatement) (lice:bool): UrsusStatement
| UFunCall (callable_object: lValue) (args: list rValue): UrsusStatement
| UBreak 
| UExit
| USendStatement (contract address function_name: string) (args: list rValue) (meta_data: list (string * rValue))
| UError (error_string: string): UrsusStatement
| UAloneValue (value: lValue): UrsusStatement
.

Inductive RustASTMultiverseX: Set := 
| Macro (paths: list RustASTMultiverseX) (tokens: option (list RustASTMultiverseX))
(* | Path (segments: RustASTMultiverseX) *)
| Typed (pat: RustASTMultiverseX)
(* | SingleIdent (name: string) *)
| Lit (lit kind subdenomination: string)
| Slice (type: RustASTMultiverseX)
| Ident (name: string) (arguments: option (list RustASTMultiverseX))
(* | Segments (tokens: list RustASTMultiverseX ) *)
| Pat (indent: string) (ty: RustASTMultiverseX)
| Let (pat: RustASTMultiverseX) (init: RustASTMultiverseX)
| LetTyped (ident type: RustASTMultiverseX) (init: RustASTMultiverseX)
| Expr (inner: list RustASTMultiverseX)
| MethodCall (receiver (*body/expression*): RustASTMultiverseX) (call_name: string) (args: list RustASTMultiverseX)
| Call (func: RustASTMultiverseX) (args: list RustASTMultiverseX )
| Reference (expr: RustASTMultiverseX)
| Stmnts (statements: list RustASTMultiverseX)
| RustType (type: RustASTMultiverseX)
| Tuple (elems: list RustASTMultiverseX)
| Error (str: string) 
| Closure (inputs: list RustASTMultiverseX) (body: RustASTMultiverseX)
| Binary (op: string) (left' right' : RustASTMultiverseX)
| Unary (op: string) (object : RustASTMultiverseX)

| PunctFlag (op: string) (type: string)
| GroupFlag
(* | Ident (ident: string) (args: option (list RustASTMultiverseX)) *)
(* | LitFlag (str: string) *)
.

Fixpoint Json2RustASTMultiverseX (ast: json) : RustASTMultiverseX := 
let fix iter_macro m path tokens : (list RustASTMultiverseX) * (option (list RustASTMultiverseX)) := 
    match m with 
    | mapkv "path" (json_map (mapkv "segments" (json_list l') _)) m' => 
        iter_macro m' (map Json2RustASTMultiverseX l') tokens
        (* iter_macro m' (map (fun item => SingleIdent(item --> "ident"!)) l' ) tokens *)
    | mapkv "tokens" (json_list l') _ => (path, Some (map (Json2RustASTMultiverseX) l'))
    | mapkv _ _ m' => iter_macro m' path tokens
    | empty => (path, None)
    end
in
match ast with 
| json_data _ => Error "json_data"
| json_list _ => Error "it haven't handled yet"
| json_map m =>
    match m with
    | (mapkv "binary" (json_map (mapkv "left" (left') (mapkv "op" (json_data op) (mapkv "right" (right') empty)) )) empty) => 
        Binary op (Json2RustASTMultiverseX left') (Json2RustASTMultiverseX right')
    | (mapkv "unary" (json_map (mapkv "op" (json_data op) (mapkv "expr" expr _))) empty) => 
        Unary op (Json2RustASTMultiverseX expr)
    | (mapkv "closure" (json_map (mapkv "inputs" (json_list inputs) (mapkv "output" (json_data output) (mapkv "body" (body) empty)) )) empty) => 
        Closure (map Json2RustASTMultiverseX inputs) (Json2RustASTMultiverseX body)
    | (mapkv "ident" (json_data v) empty) => Ident v None
    | (mapkv "lit" (json_data v) empty) => Lit v "string" ""
    | (mapkv "punct" (json_map (mapkv "op" (json_data v1) (mapkv "spacing" (json_data v2) _))) _) => PunctFlag v1 v2
    | (mapkv "group" _ _) => GroupFlag
    | mapkv "list" (json_map m') m'' => 
        let '(paths, tokens) := iter_macro m' ([Error "urecognized macro (2)"]) ([Error "haven't been recognized sequence (2)"])
        in
        Macro paths tokens
    | mapkv "lit" (json_map (mapkv "byte_str" (json_data value) empty)) _ => 
        Lit value "string" ""
    | mapkv "slice" v _ => Slice (Json2RustASTMultiverseX v)
    | mapkv "tuple" (json_map (mapkv "elems" (json_list l) _ )) _ =>
        Tuple (map Json2RustASTMultiverseX  l)
    | mapkv "reference" v _ =>
        Reference (Json2RustASTMultiverseX v)
    | mapkv "call" (json_map (mapkv "func" v1 (mapkv "args" (json_list l) _))) _ =>
        Call (Json2RustASTMultiverseX v1) (map Json2RustASTMultiverseX l)
    | mapkv "method_call" (json_map (mapkv "receiver" v1 (mapkv "method" (json_data v2) (mapkv "args" (json_list l) _))) ) _ =>
        MethodCall (Json2RustASTMultiverseX v1) v2 (map Json2RustASTMultiverseX l)
    | mapkv "expr" v _ => 
        match v with 
        | json_list l => Expr (map Json2RustASTMultiverseX l)
        | _ => Expr [Json2RustASTMultiverseX v]
        end
    | mapkv "let" 
        (json_map   (mapkv "pat" 
                        (json_map (mapkv "type" 
                                (json_map (mapkv "pat" v1 (mapkv "ty" v11 _))) _)) 
                    (mapkv "init" v2 _))) _ => 
        LetTyped  (Json2RustASTMultiverseX v1) (Json2RustASTMultiverseX v11) (Json2RustASTMultiverseX v2)
    | mapkv "let" (json_map (mapkv "pat" v1 (mapkv "init" v2 _))) _ => 
        Let (Json2RustASTMultiverseX v1) (Json2RustASTMultiverseX v2)
    | mapkv "ident" (json_map (mapkv "ident" (json_data ident) empty)) (empty) => Ident ident None
    | mapkv "ident" (json_data ident) 
        (mapkv "arguments" 
                    (json_map 
                    (mapkv "angle_bracketed" 
                            (json_map (mapkv "args" (json_list l) empty)) _ )) empty) => 
        Ident ident (Some (map Json2RustASTMultiverseX l))
    (* | mapkv "elem" (json_list l) _ => Tuple (map Json2RustASTMultiverseX l) *)
    | mapkv "type" v m' => Json2RustASTMultiverseX v
    | mapkv "typed" v m' => Json2RustASTMultiverseX v
    (* | mapkv "type" v m' => Json2RustASTMultiverseX v *)
    | mapkv "macro" (json_map m') m'' => 
        let '(paths, tokens) := iter_macro m' ([Error "urecognized macro (2)"]) ([Error "haven't been recognized sequence (2)"])
        in
        Macro paths tokens
    | mapkv "pat" v1 (mapkv "ty" v2 _) => 
        let ident := ((v1 --> "ident"?) --> "ident"!) 
        in
        match ident with 
        | "" => Error "Pat is empty"
        | _ => Pat ident (Json2RustASTMultiverseX v2)
        end
    | mapkv "path" (json_map (mapkv "segments" (json_list l) _)) m'  => 
        (* here is m, not m' *)
        let '(paths, tokens) := iter_macro m ([Error "urecognized macro (2)"]) ([Error "haven't been recognized sequence (2)"])
        in
        Macro paths tokens
        (* match tokens with 
        | nil => Macro paths None
        | _ => Macro paths (Some tokens)
        end *)
        (* SingleIdent (String.concat ",," (map (fun j => (j --> "ident"!)) l)) *)
    (* | mapkv "segments" (json_list l) m' => Segments (map Json2RustASTMultiverseX l) *)
    | mapkv _ _ _ => Error "unrecognized block"
    | empty => Error "empty map"
    end
end
.

Definition print_TokenFlag (token: RustASTMultiverseX): string := 
match token with 
| PunctFlag op type => "Operation:(" ++ op ++ ")"
| GroupFlag => "Group"
| Ident ident _ => "Ident:(" ++ ident ++ ")"
(* | LitFlag ident => """"++ ident++"""" *)
| _ => "RustObject"
end
.

(* 
Token priority
1. (,)

8. 
9. (==) need to handle from '=', '=' to '=='
10. (.)
...
*)

Fixpoint unite_some_tokens (tokens: list (rValue * RustASTMultiverseX)) (acc: list (rValue *RustASTMultiverseX)):= 
match tokens with 
| (_,(PunctFlag "=" "joint")) :: (_,(PunctFlag "=" "alone")) :: rest => 
    unite_some_tokens rest ((rError "",PunctFlag "==" "alone") :: acc)
| (_,(PunctFlag "=" "alone")) :: (_,(PunctFlag "=" "joint")) :: rest => 
    unite_some_tokens rest ((rError "",(PunctFlag "==" "alone")) :: acc)
| (_,(PunctFlag ":" "joint")) :: (_,(PunctFlag ":" "alone")) :: rest => 
    unite_some_tokens rest ((rError "",PunctFlag "." "alone") :: acc)
| (_,(PunctFlag ":" "alone")) :: (_,(PunctFlag ":" "joint")) :: rest => 
    unite_some_tokens rest ((rError "",PunctFlag "==" "alone") :: acc)
| head :: rest => unite_some_tokens rest (head::acc)
| nil => rev' acc
end
.

(* Definition check_is_unit (tokens: list TokenFlag) : bool :=
    fold_left (fun acc el => acc && (not (token_eqb el (PunctFlag "==" "alone")))) tokens true
. *)

Definition token_priority_le (token1 token2: RustASTMultiverseX): bool := 
match token1, token2 with 
| PunctFlag "." "alone", PunctFlag "==" "alone" => true
| PunctFlag "==" "alone", PunctFlag "." "alone" => false
| _, PunctFlag _ _ => true 
(* | PunctFlag _ _, PunctFlag _ _ => false *)
| _,_ => false
end
.
(* FIXME: make handling "smarter" *)
Definition get_priority_operation (tokens: list RustASTMultiverseX): option RustASTMultiverseX :=
fold_left 
(
    fun acc el => 
    match acc with 
    | None => Some el
    | Some el' => 
        if token_priority_le el' el 
        then Some el 
        else Some el'
    end
)
tokens
None
.
Definition token_eqb (token1 token2: RustASTMultiverseX):bool := 
match token1, token2 with 
| PunctFlag op1 type1, PunctFlag op2 type2 =>
    (String.eqb op1 op2) && (String.eqb type1 type2)
| GroupFlag, GroupFlag => true
(* | Ident ident1 _, Ident ident2 _ => String.eqb ident1 ident2 *)
| _, _ => false
end
.
(* let check *)
Fixpoint toMemberAccess (tokens_list : list (rValue * RustASTMultiverseX)) : (rValue * bool) := 
match tokens_list with 
| (_,(Ident ident None)) :: nil => (rIdent ident, false)
| (_, (Ident ident (Some _))) :: nil => 
    (rFunCall (rIdent ident) nil "", false)
| (_,(Ident ident None)) :: (_, (PunctFlag "." "alone")) :: rest => 
     let '(object, lice) := (toMemberAccess rest) 
    in
    (*match object with 
    | rIdent "self" => rIdent ident
    | _ =>  *)
    (rField object ident, false)
    
| (_, (Ident ident (Some _))) :: (_, (PunctFlag "." "alone")) :: rest => 
    let '(inner, lice) := (toMemberAccess rest) in
    (rFunCall (rField inner (ident)) (nil) "", lice)
| (_, GroupFlag) :: rest => 
    let '(inner, lice) := (toMemberAccess rest) in
    (rFunCall inner nil "", lice)
| _ => (rError "fail to covert tokens to rValue", true)
end.
(* in *)
Fixpoint split_tokens_by_token 
                                (tokens: list (rValue *RustASTMultiverseX)) 
                                (acc: list (list (rValue *RustASTMultiverseX))) 
                                (curr: list (rValue *RustASTMultiverseX)) 
                                (token: RustASTMultiverseX) : list (list (rValue *RustASTMultiverseX)) := 
match tokens with 
| head :: rest => 
    if token_eqb (snd head) token
    then 
        split_tokens_by_token rest ((rev' curr) ::acc) nil token
    else
        split_tokens_by_token rest (acc) (head::curr) token
| nil => 
    match curr with 
    | nil => rev' acc
    | _ => rev' ((rev' curr) :: acc)
    end
end.

Fixpoint Tokens2rValue (tokens: list (rValue * RustASTMultiverseX)) (depth: nat): (rValue*bool) := 
match depth with 
| O => (rError "Fail to handle token sequence", true)
| S n => 
    let tokens := unite_some_tokens tokens nil 
    in
    let operation := get_priority_operation (map snd tokens) 
    in
    match operation with 
    | Some (PunctFlag "." "alone") => 
        toMemberAccess (rev' tokens)
        (* rIdent ((String.concat ";" (map print_TokenFlag tokens))) *)
    | Some (Ident ident _) =>
        (rIdent ident, false)
    | Some (PunctFlag "==" "alone") =>
        let operation := (PunctFlag "==" "alone") 
        in
        match (split_tokens_by_token tokens nil nil operation) with 
        | head1 :: head2 :: nil => 
            let '(left', left_lice) := Tokens2rValue head1 n
            in
            let '(right', right_lice) := Tokens2rValue head2 n
            in
            (rBinOperation "==" left' right', left_lice || right_lice)
        | _ => (rError "hasn't expected not binary operation", true)
        end
    | Some (Lit lit_string kind _) =>
        (rLiteral lit_string kind "", false)
    (* | Some (Ident ident _) =>
        (rIdent ident) *)
    | Some op => 
        (rError ("op("++(print_TokenFlag op)++") hasn't been added yet"), true)
    | None => (rError "empty tokenlist", true)
    end
end.

Fixpoint RustASTMultiverseX2rValue (ast: RustASTMultiverseX): (rValue*bool) := 
match ast with 
| Lit value kind sub => (rLiteral value kind sub, false)
| Slice inner => 
    let '(inner, lice):= (RustASTMultiverseX2rValue inner)
    in
    (rSliceMod inner, lice) 
| Macro (paths (* : list RustASTMultiverseX*) ) (tokens (* : list RustASTMultiverseX*) ) => 
    (* let rValued_tokens := map RustASTMultiverseX2rValue tokens 
    in *)
    let fix handleTokenToTokenArgs tokens acc curr : list (list (rValue * RustASTMultiverseX)) := 
        match tokens with 
        | nil => 
            match curr with 
            | nil => rev' acc
            | _ => rev' ((rev' curr) :: acc)
            end
        | (PunctFlag "," "alone") :: rest => handleTokenToTokenArgs rest ((rev' curr) :: acc) []
        | head :: rest => 
            let '(head_rValued, _) := RustASTMultiverseX2rValue head 
            in
            handleTokenToTokenArgs rest acc ((head_rValued, head)::curr)
        end
    in
    match tokens with
    | Some tokens =>
        let handled_tokens := 
            map
            (fun tokens_list =>
                
                (* rTuple (map fst tokens_list) *)
                (* toMemberAccess tokens_list *)
                Tokens2rValue (tokens_list) 10
                
            )
            (handleTokenToTokenArgs tokens [] [])
        in
        let '(callable_object, lice_object) := 
            let fix member_access paths: rValue * bool := 
                match paths with 
                | nil => (rError "empty paths", true)
                | (head) :: nil => (RustASTMultiverseX2rValue head)
                | (Ident head _) :: tail => 
                    let '(object, lice) := member_access tail 
                    in
                    (* match object with 
                    | rIdent "self" => 
                        rIdent head
                    | _ => *)
                        (rField object head, lice)
                    (* end *)
                | _ => (rError "empty paths", true)
                end
            in
            member_access paths
            (* (RustASTMultiverseX2rValue paths) *)
        in
        let args := map fst (handled_tokens)
        in
        let lice := 
            orb 
            lice_object
            (fold_left
            orb
            (map snd handled_tokens)
            false)
        in
        (rFunCall callable_object args "functionCall" , lice)
    | None =>
        let '(callable_object, lice_object) := 
            let fix member_access paths: rValue * bool := 
                match paths with 
                | nil => (rError "empty paths", true)
                | (head) :: nil => (RustASTMultiverseX2rValue head)
                | (Ident head _) :: tail => 
                    let '(object, lice) := member_access tail 
                    in
                    (* match object with 
                    | rIdent "self" => 
                        rIdent head
                    | _ => *)
                        (rField object head, lice)
                    (* end *)
                | _ => (rError "empty paths", true)
                end
            in
            member_access paths
            (* (RustASTMultiverseX2rValue paths) *)
        in
        (callable_object,lice_object)
    end
(* | Path (segments (* : RustASTMultiverseX*) ) => 
    RustASTMultiverseX2rValue segments *)
| Typed (pat (* : RustASTMultiverseX*) ) => 
    RustASTMultiverseX2rValue pat
| Pat (indent (* : string*) ) (ty (* : RustASTMultiverseX*) ) => 
    (rIdent (indent ++ " (* from pat *)" ), true)
| Ident (name (* : string*) ) (arguments (* : list RustASTMultiverseX*) ) => 
    match arguments with 
    | None => (rIdent name, false)
    | Some arguments => 
        let args_lices := (map RustASTMultiverseX2rValue arguments) 
        in
        let lice := 
            fold_left
            orb
            (map snd args_lices)
            false
        in
        (rFunCall (rIdent name) (map fst args_lices) "functionCall", lice)
    end
(* | SingleIdent name => 
    rIdent name *)
(* | Segments (tokens (* : list RustASTMultiverseX *) ) => 
    rError "Segments deprecated" *)
| LetTyped _ _ _ =>
    (rError "Let can't be in rValue", true)
| Let (pat (* : RustASTMultiverseX*) ) (init (* : RustASTMultiverseX*) ) => 
    (rError "Let can't be in rValue", true)
| Expr (inner (* : list RustASTMultiverseX*) ) => 
    match inner with 
    | head :: _ => RustASTMultiverseX2rValue head 
    | _ => (rError "Expr failed", true)
    end
| MethodCall (receiver (*body/expression*: RustASTMultiverseX*) ) (call_name (* : string*) ) (args (* : list RustASTMultiverseX*) ) => 
        let args_lices := (map RustASTMultiverseX2rValue args) 
        in
        let lice := 
            fold_left
            orb
            (map snd args_lices)
            false
        in
        let '(inner, lice_inner) := 
            (RustASTMultiverseX2rValue receiver)
        in
        (rFunCall (rField inner call_name) (map fst args_lices) "functionCall", orb lice lice_inner)

| Call (func (* : RustASTMultiverseX*) ) (args (* : list RustASTMultiverseX *) ) => 
        let '(inner, lice_inner) := 
        (RustASTMultiverseX2rValue func)
        in
        let args_lices := (map RustASTMultiverseX2rValue args) 
        in
        let lice := 
            fold_left
            orb
            (map snd args_lices)
            false
        in
        (rFunCall inner (map fst args_lices) "functionCall", orb lice_inner lice)
| Reference (expr (* : RustASTMultiverseX*) ) => 
    (*rReferenceMod*) (RustASTMultiverseX2rValue expr)
| Stmnts (statements (* : list RustASTMultiverseX*) ) => 
    (rError "statements isn't possible to interpret in rValue", true)
| RustType (type (* : RustASTMultiverseX*) ) => 
    (rError "RustType", true)
| PunctFlag op _ =>
    (rError "PunctFlag", true)
| GroupFlag =>
    (rError "GroupFlag", true)
| Closure inputs body => 
    let arg_lice := (map RustASTMultiverseX2rValue inputs) 
    in
    let '(body, body_lice) := (RustASTMultiverseX2rValue body) 
    in
    let lice := 
        fold_left
        orb
        (map snd arg_lice)
        false
    in
    (rLambda (map fst arg_lice) (rError "(* returns nothing *)") body, orb body_lice lice)
| Binary op left' right' => 
    let '(left', left_lice) := (RustASTMultiverseX2rValue left') 
    in 
    let '(right', right_lice) := (RustASTMultiverseX2rValue right') 
    in
    (rBinOperation op left' right', orb left_lice right_lice)
| Unary op object =>
    let '(object, lice) := (RustASTMultiverseX2rValue object) 
    in
    (rUnOperation true op object, lice)
(* | Ident _ _ =>
    rError "Ident" *)
(* | LitFlag _ =>
    rError "LitFlag" *)
| Tuple (elems (* : list string*) ) => 
    let elems_lices := (map RustASTMultiverseX2rValue elems) 
    in
    let lice := 
        fold_left
        orb
        (map snd elems_lices)
        false
    in
    (rTuple (map fst elems_lices) , lice)
| Error (str (* : string*) ) => (rError str, true)
end
.




Fixpoint RustASTMultiverseX2lValue (ast: RustASTMultiverseX): (lValue * bool) := 
match ast with 
| Slice _ => (lError "Slice can't be in lValue", true)
| Lit _ _ _ => (lError "literal can't be in lValue", true)
| Macro (paths (* : RustASTMultiverseX*) ) (tokens (* : list RustASTMultiverseX*) ) => 
    let fix handleTokenToTokenArgs tokens acc curr : list (list (rValue * RustASTMultiverseX)) := 
    match tokens with 
    | nil => 
        match curr with 
        | nil => rev' acc
        | _ => rev' ((rev' curr) :: acc)
        end
    | (PunctFlag "," "alone") :: rest => handleTokenToTokenArgs rest ((rev' curr) :: acc) []
    | head :: rest => 
        let '(head_rValued, _) := RustASTMultiverseX2rValue head 
        in
        handleTokenToTokenArgs rest acc ((head_rValued, head)::curr)
    end
    in
    match tokens with
    | Some tokens =>
        let handled_tokens := 
            map
            (fun tokens_list =>
                
                (* rTuple (map fst tokens_list) *)
                (* toMemberAccess tokens_list *)
                Tokens2rValue (tokens_list) 10
                
            )
            (handleTokenToTokenArgs tokens [] [])
        in
        let (callable_object, object_lice):= 
            let fix member_access paths := 
                match paths with 
                | nil => (lError "empty paths", true)
                | head :: nil => RustASTMultiverseX2lValue head
                | (Ident head _) :: tail => 
                    let '(inner, lice) := 
                        member_access tail
                    in 
                    (lField inner head, lice)
                | _ => (lError "empty paths", true)
                end
            in
            member_access paths
            (* (RustASTMultiverseX2rValue paths) *)
        in
        let args := (map fst handled_tokens)
        in
        let lice := 
            fold_left
            orb
            (map snd handled_tokens)
            false
        in
        (lFunCall callable_object args, orb lice object_lice)
    | None =>
        let (callable_object, object_lice):= 
        let fix member_access paths := 
                match paths with 
                | nil => (lError "empty paths", true)
                | head :: nil => RustASTMultiverseX2lValue head
                | (Ident head _) :: tail => 
                    let '(inner, lice) := (member_access tail)
                    in 
                    (lField inner head, lice)
                | _ => (lError "empty paths", true)
                end
            in
            member_access paths
            (* (RustASTMultiverseX2rValue paths) *)
        in
        (callable_object, object_lice)
    end
(* | Path (segments (* : RustASTMultiverseX*) ) => 
    RustASTMultiverseX2lValue segments *)
| Typed (pat (* : RustASTMultiverseX*) ) => 
    (lError "Typed can't be in lValue", true)
| Pat (indent (* : string*) ) (ty (* : RustASTMultiverseX*) ) => 
    (lError "Pat can't be in lValue", true)
| Ident (name (* : string*) ) (arguments (* : list RustASTMultiverseX*) ) => 
    match arguments with 
    | None => (lIdent name, false)
    | Some arguments => 
        let args_lices := (map RustASTMultiverseX2rValue arguments) 
        in
        let lice := 
            fold_left
            orb
            (map snd args_lices)
            false
        in
        (lFunCall (lIdent name) (map fst args_lices), lice)
    end
(* | SingleIdent name => 
    lIdent name *)
(* | Segments (tokens (* : list RustASTMultiverseX *) ) => 
    lError "Segments deprecated" *)
| LetTyped _ _ _ =>
    (lError "Let shouldn't be in lvalue", true)
| Let (pat (* : RustASTMultiverseX*) ) (init (* : RustASTMultiverseX*) ) => 
    (lError "Let shouldn't be in lvalue", true)
| Expr (inner (* : list RustASTMultiverseX*) ) => 
    match inner with 
    | head :: _ => RustASTMultiverseX2lValue head 
    | _ => (lError "Expr failed", true)
    end
| MethodCall (receiver (*body/expression*: RustASTMultiverseX*) ) (call_name (* : string*) ) (args (* : list RustASTMultiverseX*) ) => 
    (* let object := (RustASTMultiverseX2lValue receiver) 
    in
    match object with 
    | lIdent "self" => 
        lFunCall (lIdent call_name) (map RustASTMultiverseX2rValue args) 
    | _ =>  *)
        let '(inner, lice_inner):=(RustASTMultiverseX2lValue receiver)
        in
        let args_lices := (map RustASTMultiverseX2rValue args) 
        in
        let lice := 
            fold_left
            orb
            (map snd args_lices)
            false
        in
        (lFunCall (lField inner call_name) (map fst args_lices), orb lice lice_inner)
    (* end *)
| Call (func (* : RustASTMultiverseX*) ) (args (* : list RustASTMultiverseX *) ) => 
    let '(inner, lice_inner):=(RustASTMultiverseX2lValue func)
    in
    let args_lices := (map RustASTMultiverseX2rValue args) 
    in
    let lice := 
        fold_left
        orb
        (map snd args_lices)
        false
    in
    (lFunCall inner (map fst args_lices), orb lice lice_inner)
| Reference (expr (* : RustASTMultiverseX*) ) => 
    (lError "Reference can't be in lValue", true)
| Stmnts (statements (* : list RustASTMultiverseX*) ) => 
    (lError "Statements can't be in lValue", true)
| RustType (type (* : RustASTMultiverseX*) ) => 
    (lError "RustType can't be in lValue", true)
| Tuple (elems (* : list string*) ) => 
    (lError "Tuple haven't added yet", true)
| PunctFlag _ _ =>
    (lError "PunctFlag", true)
| GroupFlag =>
    (lError "GroupFlag", true)
| Closure _ _ =>
    (lError "Closure", true)
| Binary _ _ _ =>
    (lError "Binary", true)
| Unary _ _ =>
    (lError "Unary", true)
(* | Ident _ _ =>
    lError "Ident" *)
(* | LitFlag _ =>
    lError "LitFlag" *)
| Error (str (* : string*) ) => (lError str, true)
end
.


Fixpoint RustASTMultiverseX2UrsusStatement (ast: RustASTMultiverseX): (UrsusStatement * bool) := 
match ast with
| Slice _ => (UError "slice can't be as UrsusStatement", true)
| Lit _ _ _ => (UError "lit can't be as UrsusStatement", true)
| Macro (paths (* : RustASTMultiverseX*) ) (tokens (* : list RustASTMultiverseX*) ) => 
    let fix handleTokenToTokenArgs tokens acc curr : list (list (rValue * RustASTMultiverseX)) := 
    match tokens with 
    | nil => 
        match curr with 
        | nil => rev' acc
        | _ => rev' ((rev' curr) :: acc)
        end
    | (PunctFlag "," "alone") :: rest => handleTokenToTokenArgs rest ((rev' curr) :: acc) []
    | head :: rest => 
        let '(head_rValued, _) := RustASTMultiverseX2rValue head 
        in
        handleTokenToTokenArgs rest acc ((head_rValued, head)::curr)
    end
    in
    let handled_tokens := 
        match tokens with 
        | Some tokens =>
            map
            (fun tokens_list =>
                
                Tokens2rValue tokens_list 10
                (* rError "token" *)
            )
            (handleTokenToTokenArgs tokens [] [])
        | None => nil
        end
    in
    let (callable_object, object_lice):= 
            let fix member_access paths := 
                match paths with 
                | nil => (lError "empty paths", true)
                | head :: nil => RustASTMultiverseX2lValue head
                | (Ident head _) :: tail => 
                    let '(inner, lice) := 
                        member_access tail
                    in 
                    (lField inner head, orb lice (String.eqb head "update"))
                | _ => (lError "empty paths", true)
                end
            in
            member_access paths
            (* (RustASTMultiverseX2rValue paths) *)
    in
    let args := (map fst handled_tokens)
    in
    let lice := 
        fold_left
        orb
        (map snd handled_tokens)
        false
    in
    (UFunCall callable_object args, orb lice object_lice)
| Typed (pat (* : RustASTMultiverseX*) ) => (UError "typed", true)
| Pat (indent (* : string*) ) (ty (* : RustASTMultiverseX*) ) => (UError "Pat", true)
| Ident (name (* : string*) ) (arguments (* : list RustASTMultiverseX*) ) => (UError "just ident", true)
(* | SingleIdent name => UError "single ident" *)
(* | Segments (tokens : list RustASTMultiverseX ) => UError "segments" *)
| LetTyped ident type init =>
    let '(ident, ident_lice) := RustASTMultiverseX2lValue ident in 
    let '(type, type_lice) := RustASTMultiverseX2rValue type in
    let '(init, init_lice) := (RustASTMultiverseX2rValue init) in
    (UVarDeclaration [( ident, type)] init, orb (orb ident_lice type_lice) init_lice)
| Let (pat (* : RustASTMultiverseX*) ) (init (* : RustASTMultiverseX*) ) => 
    let '(ident, ident_lice) := RustASTMultiverseX2lValue pat in 
    (* let '(type, type_lice) := RustASTMultiverseX2rValue type in *)
    let '(init, init_lice) := (RustASTMultiverseX2rValue init) in
    (UVarDeclaration [(ident , rError "Error: handling type haven't supported yet")] init, true)
| Expr (inner (* : list RustASTMultiverseX*) ) => 
    match inner with 
    | head :: _ => 
        RustASTMultiverseX2UrsusStatement head
    | _ => (UError "Expr haven't recognized", true)
    end
| MethodCall (receiver (*body/expression*: RustASTMultiverseX*) ) (call_name (* : string*) ) (args (* : list RustASTMultiverseX*) ) => 
    let '(inner, lice_inner) := (RustASTMultiverseX2lValue receiver) 
    in
    let args_lices := (map RustASTMultiverseX2rValue args)
    in
    let lice := 
        fold_left
        orb
        (map snd args_lices)
        false
    in
    (UFunCall (lField inner call_name) (map fst args_lices), orb (orb lice lice_inner) (String.eqb call_name "update"))
    
| Call (func (* : RustASTMultiverseX*) ) (args (* : list RustASTMultiverseX *) ) => 
    let '(inner, lice_inner) := (RustASTMultiverseX2lValue func)
    in
    let args_lices := (map RustASTMultiverseX2rValue args)
    in
    let lice := 
        fold_left
        orb
        (map snd args_lices)
        false
    in
    (UFunCall inner (map fst args_lices), (orb lice lice_inner) (*call_name =? "update"*))
| Reference (expr (* : RustASTMultiverseX*) ) => (UError "reference haven't added yet", true)
| Stmnts (statements (* : list RustASTMultiverseX*) ) => 
    let (statements, lice) := 
        fold_left 
        (fun acc el => 
            let '(acc, lice) := acc 
            in
            match el with 
            | (UError _, new_lice) => (acc, false)
            | (UBlock another_statements, new_lice) =>
                (app (rev' another_statements) acc, orb lice new_lice)
            | (el, new_lice) => ((el) :: acc, orb lice new_lice)
            end 
        )
        (map RustASTMultiverseX2UrsusStatement statements)
        (nil, false)
    in
    (UBlock (rev' statements), lice)
| RustType (type (* : RustASTMultiverseX*) ) => (UError "haven't added yet", true)
| Tuple (elems (* : list string*) ) => (UError "haven't added yet", true)
| PunctFlag _ _ =>
    (UError "PunctFlag", true)
| GroupFlag =>
    (UError "GroupFlag", true)
| Closure _ _ =>
    (UError "Closure", true)
| Binary _ _ _ =>
    (UError "Binary", true)
| Unary _ _ =>
    (UError "Binary", true)
(* | Ident _ _ =>
    UError "Ident" *)
(* | LitFlag _ =>
    UError "LitFlag" *)
| Error (str (* : string*) ) => (UError "haven't added yet", true)
end
.

Definition key_word_wrapper (identifier:string) : string := 
match identifier with 
| "id" => "{id}"
| "value" => "{value}"
| "f1" => "{f1}"
| "f2" => "{f2}"
| "index" => "{index}"
| "condition" => "{condition}"
| "require" => "require_"
| "revert" => "revert_"
| _ => identifier
end
.
Definition key_word_wrapperL (identifier:string):string := 
match identifier with 
| "require" => "require_"
| "revert" => "revert_"
| _ => identifier
end
.

Fixpoint print_rValue (object: rValue): string :=
match object with 

| rSliceMod type => "[" ++ (print_rValue type) ++ "]"
| rCond cond true_val false_val => 
    (print_rValue cond) ++ " ? " ++
    (print_rValue true_val) ++ " : " ++
    (print_rValue false_val)
| rIdent name => 
    key_word_wrapper name
| rLiteral literal' kind subdenomination => 
    match kind with 
    | "number" => 
        "{"++literal' ++ (if subdenomination=? "" then "" else " " ++ subdenomination) ++ "}"
    | "string" => 
        "{"++""""++ (replaceWith [("\", "")] literal') ++ """" ++ "}"
    | _ => 
        "{"++literal' ++ (if subdenomination=? "" then "" else " " ++ subdenomination) ++ "}"
    end
| rTypeIdent type => xtype false type
| rBinOperation operation left' right' => 
    "("++(print_rValue left') ++ operation ++ (print_rValue right') ++ ")"
| rUnOperation is_prefix operation object => 
    match is_prefix with 
    | true => operation ++ " " ++ (print_rValue object)
    | false => (print_rValue object) ++ " " ++ operation
    end
| rField object member =>
    (print_rValue object) ++ "->" ++ member
| rIndex object index =>
    (print_rValue object) ++ "[" ++ (print_rValue index) ++ "]"
| rTuple objects =>
    match objects with 
    | nil => ""
    | item :: nil => print_rValue item
    | _ => "[" ++ String.concat ", " (map print_rValue objects) ++ "]"
    end
| rFunCall callable_object args kind =>
    match kind with
    | "structConstructorCall" =>
        "(* "++(print_rValue callable_object) ++ " *)" ++ 
        " [" ++ (String.concat "," (map print_rValue args)) ++ "]"
    | _ =>
        ((print_rValue callable_object) ++ (if (kind =? "typeConversion") then  "" else "") ++
        "(" ++ (String.concat "," (map print_rValue args)) ++ ")")
    end
| rReferenceMod expr => "&" ++ (print_rValue expr)
| rLambda inputs output body => 
    "fun " ++ (String.concat " " (map print_rValue inputs)) ++ "=>" ++
    " // " ++ (print_rValue body) ++ " // "
| rError error_string =>
    " (* -> *) " ++ error_string  ++ " (* <- *) "
end    
.
Fixpoint print_lValue (object: lValue): string :=
match object with
| lField object member => (print_lValue object) ++ "->" ++ member
| lIndex object index => (print_lValue object) ++ "[[" ++ (print_rValue index) ++ "]]"
| lTuple objects => "[" ++ (String.concat ", " (map print_lValue objects)) ++ "]"
| lFunCall callable_object args => (print_lValue callable_object) ++ "(" ++ (String.concat ", " (map print_rValue args)) ++ ")"
| lIdent name => 
    key_word_wrapperL name
| lUnOperation is_prefix operation object =>
    match is_prefix with 
    | true => operation ++ " " ++ (print_lValue object)
    | false => (print_lValue object) ++ " " ++ operation
    end
| lError error_string => 
" (* -> *) " ++ error_string  ++ " (* <- *) "
end
.


Definition state := bool (* refine *) * string (* indent *) * bool (* is_last *).
Fixpoint print_UrsusStatement (statement: UrsusStatement) (s:state): string := 
let '(refine, indent, is_last) := s in
match statement with 
| UExit => 
    (if refine then (\n""++indent++":://  ") else "") ++
    "exit_ {} " ++
    (if refine then" |." else "")
| UBreak =>
    (if refine then (\n""++indent++":://  ") else "") ++
    "break_" ++
    (if refine then " |." else "")
| UFor_loop condition initialization_expression loop_expression body lice =>
(if refine then (\n""++indent++":://  ") else "") ++
    "for (" ++ 
    (print_UrsusStatement initialization_expression (false, indent, false)) ++ " , " ++
    (print_rValue condition) ++ " , " ++
    (print_UrsusStatement loop_expression (false, indent, false)) ++
    " ) do { {_:UExpression _  "++(if lice then "true" else "false")++"} }  " ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    print_UrsusStatement body (true, indent, false)
| UWhile_loop condition body lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    "while (" ++ print_rValue condition ++ ") do { {_:UExpression _  "++
    (if lice then "true" else "false")++"} }" ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    print_UrsusStatement body (true, indent, false)
| UForeach_loop range_declaration range_expression body lice =>
    (if refine then (\n""++indent++":://  ") else "") ++
    "for ( [" ++ String.concat ", " (map (fun item => "'"++item)range_declaration) ++ "] in " ++ 
    print_rValue range_expression ++ ")" ++
    " do { {_:UExpression _  "++(if lice then "true" else "false")++"} }  " ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    
    print_UrsusStatement body (true, indent, false)
| UIf_Then cond true_body cond_lice lice_then =>
    (if refine then (\n""++indent++":://  ") else "") ++ 
    "if (" ++ (print_rValue cond) ++ ") then { { _ : UExpression _ "++(if lice_then then "true" else "false")++"} } " ++
    (if refine then (if is_last then " |" else "")++"." else "") ++
    print_UrsusStatement true_body (true, indent, false)
| UIf_Then_Else cond true_body false_body cond_lice lice_then lice_else =>
    (if refine then (\n""++indent++":://  ") else "") ++ 
    "if (" ++ (print_rValue cond) ++ ") then { { _:UExpression _ "++
    (if lice_then then "true" else "false")++" } } else { { _:UExpression _ "++(if lice_else then "true" else "false")++"} } " ++
    (if refine then (if is_last then " |" else "")++"." else "")++
    print_UrsusStatement true_body (true, indent, false) ++
    print_UrsusStatement false_body (true, indent, false)
| UAloneValue value =>
    (if refine then indent ++ ":://   " else "") ++
    (print_lValue value) ++
    (if refine then (if is_last then " |." else " .") else "")
| UDefaultVarDeclaration objects =>
    (if refine then indent ++ ":://   " else "") ++
    (match objects with 
    | nil => " (* error: set of variables is empty *) "
    | (var_name, object) :: nil => 
        ("var " ++ (print_lValue var_name)) ++ ": " ++ 
        (print_rValue object) 
    | _ => 
    let seq := map (fun item => print_lValue (fst item) ++ " : " ++ (xtype false (print_rValue (snd item)))) objects in
    ("var (" ++ (String.concat ", " seq) ++ ")") ++ " "
    end) ++ (if refine then " ;_|." else "")
| UVarDeclaration objects(*: list (lValue * rValue)*) value (*: rValue*) =>
    (if refine then indent ++ ":://   " else "") ++
    (match objects with 
    | nil => " (* error: set of variables is empty *) "
    | (var_name, object) :: nil => 
        ("var " ++ (print_lValue var_name)) ++ ": " ++ 
        (xtype false (print_rValue object)) ++ " := " ++ (print_rValue value)
    | _ => 
        let seq := map (fun item => print_lValue (fst item) ++ " : " ++ (xtype false (print_rValue (snd item)))) objects in
        ("var (" ++ (String.concat ", " seq) ++ ")") ++ " := " ++ (print_rValue value)
    end) ++ (if refine then " ;_|." else "")
    
| UAssignment operator left' right' => 
    let operator := 
        match operator with 
        | "=" => ":="
        | "+=" => operator
        | "-=" => operator
        | "&=" => operator
        | "|=" => operator
        | "/=" => operator
        | "*=" => operator
        | _ => " (* '"++operator++"' assignment hasn't been supported yet *) "
        end
    in
    (if refine then indent ++ ":://   " else "") ++
    (print_lValue left') ++ " " ++ 
    operator ++ " " ++
    (print_rValue right') ++
    (if refine then (if is_last then " |." else " .") else "")
| UFunCall callable_object args =>
    (if refine then indent ++ ":://   " else "") ++
    let args_string := 
        match callable_object with 
        | lIdent "require" => 
            match args with 
            | [status; rLiteral val kind subdenomination] =>
                let val := 
                    match kind with 
                    | "string" => """"++val++""""
                    | _ => val
                    end    
                in
                (print_lValue callable_object) ++ "(" ++ (print_rValue status) ++ ", " ++ "#{" ++ val ++ "}" ++ ")"
            | _ => 
                (print_lValue callable_object) ++ "(" ++ (String.concat ", " (map print_rValue args)) ++ ")"
            end
        | lField object "transfer" =>
            "tvm->transfer(" ++ (print_lValue object)++", " ++ (String.concat ", " (map print_rValue args)) ++ ")"
        | _ => (print_lValue callable_object) ++ "(" ++ (String.concat ", " (map print_rValue args)) ++ ")"
        end
    in
    args_string ++
    (if refine then (if is_last then " |." else " .") else "")
| USendStatement contract address function_name args meta_data =>
    (if refine then (\n""++indent++":://  ") else "") ++ 
    "send " ++ contract ++ "." ++ function_name ++
    "(" ++ 
    (String.concat", " (map (fun arg => print_rValue arg) args)) ++
    ") => "++address++" with {InternalMessageParamsLRecord} [$ " ++
    (String.concat 
    "; " 
    (
        map 
        (
            fun data => let '(name, expr):= data 
            in 
            print_rValue expr  ++ "⇒" ++ "{Message_ι_" ++name++"}" 
        ) 
        meta_data
    )) ++ "$]" ++
    (if refine then (if is_last then " |" else "") ++ "." else "")
    
| UError error_string => 
    " (* -> *) " ++ error_string  ++ " (* <- *) "
| UBlock statements => 
    let fix iter statements := 
        match statements with 
        | nil => ""
        (* | (UBlock block) :: nil => iter statements *)
        (* | (UError "") :: nil => "" *)
        (* | (UBlock block) :: (UError "") :: nil =>
            iter block *)
        (* | head :: (UError "") :: nil => *)
            (* \n"" ++ print_UrsusStatement head (true, indent++"    ", true) *)
        (* | (UBlock block) :: (UError "") :: tail =>
            \n"" ++ String.concat \n"" *)
        (* | head :: (UError "") :: tail => *)
            (* \n"" ++ print_UrsusStatement head (true, indent++"    ", false) ++
            (iter tail) *)
        | head :: nil => 
            \n"" ++ print_UrsusStatement head (true, indent++"    ", true)
        | head :: tail =>
            \n"" ++ print_UrsusStatement head (true, indent++"    ", false) ++
            (iter tail)
        end
    in
    (* let fix filter_st statements {struct statements} := 
    match statements with 
    | UError _ :: rest => rest
    | head :: rest => head :: (filter_st rest)
    | nil => nil
    end 
    in *)
    \n"" ++ indent ++ "{" ++
    (iter ( statements) ) ++
    \n"" ++ indent ++ "}"
end.








(* 
List of needed stuff:
1. Contract Name
2. Sends To?
3. Fields
4. Type Defs
5. Constants
6. LocalState
*)

(* Requirements for a "Contract" 
1. Inly one contract can be in the file.
*)

(* Questions:
1. Examples with fields (or waht we called as fiels in Ursus), Type Defs
*)

Record Rust_fn := {
    name : string;
    attrs : list rValue;
    args : list (string * rValue);
    return_type: rValue;
    body: (UrsusStatement*bool);
}.

Record Context := {
    storage_mapper_list : list string;
    ident_wrapper: string -> string
}.


Definition print_rust_functions(functions: list Rust_fn) := 
String.concat
\n""
(map
(
    fun function =>
    match function with 
    | Build_Rust_fn name attrs args return_type body =>
        let args_string := 
            (String.concat ", " (map (fun arg_type => let '(name, type):= arg_type in "("++ name ++": " ++ (print_rValue type) ++")") args))
        in
        (match body with 
        | (UBlock nil, _) => 
            (* \n"#[" ++ (String.concat ", " (app (map print_rValue attrs) [print_rValue(rIdent "no_body")])) ++ "]" ++ *)
            \n"(* Ursus Definition " ++ name ++ " " ++ args_string ++ ": UExpression (" ++ (print_rValue return_type) ++ ") false. " ++
            \n"return. Defined. Sync. *)"
        | (body, lice) =>
            (* (match attrs with 
            | nil => ""
            | _ => \n"#[" ++ (String.concat ", "  (map print_rValue attrs)) ++ "]"
            end) ++ *)
            \n"Ursus Definition " ++ name ++ " " ++ args_string ++ 
            ": UExpression (" ++ (print_rValue return_type) ++ ") "++(if lice then "true" else "false")++"." ++
            (print_UrsusStatement body (false, "", false)) ++
            \n"return. Defined. Sync."
        end)   
    end
)
functions)
.
Fixpoint modify_rValue (context:Context) (object: rValue):= 
match object with 
| rSliceMod type => rSliceMod type 
| rCond cond true_val false_val => rCond cond true_val false_val 
| rIdent name => 
    let wrapper := ident_wrapper context 
    in
    rIdent (wrapper name) 
| rLiteral literal' kind subdenomination => rLiteral literal' kind subdenomination 
| rTypeIdent type => rTypeIdent type
| rBinOperation operation left' right' => 
    match operation with 
    | "+=" =>
        let mod_left := ((modify_rValue context) left') 
        in
        let mod_right := ((modify_rValue context) right')
        in
        rBinOperation ":=" mod_left (rBinOperation "+" mod_left mod_right)
    | _ => rBinOperation operation ((modify_rValue context) left') ((modify_rValue context) right')
    end
(* | rUnOperation is_prefix operation object => rUnOperation is_prefix operation ((modify_rValue context) object) *)
| rField object member => 
    match object with 
    | rIdent "self" => rIdent member
    | _ => rField ((modify_rValue context) object) member
    end
| rIndex object index => rIndex ((modify_rValue context) object) ((modify_rValue context) index)
| rTuple objects => rTuple (map (modify_rValue context) objects)
| rFunCall callable_object args kind => 
    let default_case := 
        rFunCall ((modify_rValue context) callable_object) (map (modify_rValue context) args) kind
    in
    match callable_object with 
    | rField (rFunCall (rField (rIdent "self") inner_name) args' _) member => 
        if isInList inner_name (storage_mapper_list context)
        then 
            match member with 
            | "get" =>
                let member := "svm_get" 
                in
                rFunCall (rField (rIdent inner_name) member) (map (modify_rValue context) args) kind
            | _ => 
                default_case
            end
        else
            default_case
    | rField (rFunCall (rIdent inner_name) args' _) member => 
        if isInList inner_name (storage_mapper_list context)
        then 
            match member with 
            | "get" =>
                let member := "svm_get" 
                in
                rFunCall (rField (rIdent inner_name) member) (map (modify_rValue context) args) kind
            | _ => 
                default_case
            end
        else
            default_case
    | rField (rIdent "self") member_name =>
        if isInList member_name (storage_mapper_list context)
        then 
            fold_left
            (fun acc el =>
                rIndex acc el
                )
            args
            (rIdent member_name)
        else 
            default_case
    | _ =>
        default_case
    end
(* rFunCall ((modify_rValue context) callable_object) (map (modify_rValue context) args) kind *)
| rReferenceMod expr => rReferenceMod ((modify_rValue context) expr) 
| rError error_string => rError error_string
| rUnOperation prefix op object =>
    match op with 
    | "*" =>
        ((modify_rValue context) object)
    | _ => 
        rUnOperation prefix op ((modify_rValue context) object)
    end
| rLambda inputs output body =>
    let list_of_string_ident := 
        fold_left
        (fun acc el => match el with | rIdent ident => ident :: acc | _ => acc end)
        inputs
        nil
    in
    let wrapper := ident_wrapper context 
    in
    let new_wrapper := 
        (fun ident => if isInList ident list_of_string_ident then "λ"++ident else wrapper ident) 
    in
    let new_context := Build_Context (storage_mapper_list context) new_wrapper 
    in
    rLambda (map (modify_rValue new_context) inputs) output ((modify_rValue new_context) body)
(* | ob => ob *)
end.

Fixpoint modify_lValue (context: Context) (object: lValue):= 
match object with 
| lField object member => 
    match object with 
    | lIdent "self" => lIdent member
    | _ => lField ((modify_lValue context) object) member
    end
| lIndex object index => lIndex ((modify_lValue context) object) ((modify_rValue context) index)
| lTuple objects => lTuple (map (modify_lValue context) objects)
| lFunCall callable_object args => 
    let default_case := 
        lFunCall ((modify_lValue context) callable_object) (map (modify_rValue context) args)
    in
    match callable_object with 
    | lField (lFunCall (lField (lIdent "self") inner_name) args') member => 
        if isInList inner_name (storage_mapper_list context)
        then 
            match member with 
            | "set" =>
                let member := "svm_set" 
                in
                lFunCall (lField (lIdent inner_name) member) (map (modify_rValue context) args)
            | "update" =>
                let member := "svm_update" 
                in
                lFunCall (lField (lIdent inner_name) member) (map (modify_rValue context) args)
            | _ => 
            default_case
            end
        else
            default_case
    | lField (lFunCall (lIdent inner_name) args') member => 
        if isInList inner_name (storage_mapper_list context)
        then 
            match member with 
            | "set" =>
                let member := "svm_set" 
                in
                lFunCall (lField (lIdent inner_name) member) (map (modify_rValue context) args)
            | "update" =>
                let member := "svm_update" 
                in
                lFunCall (lField (lIdent inner_name) member) (map (modify_rValue context) args)
            | _ => 
            default_case
            end
        else
            default_case
    | _ =>
        default_case
    end

| lIdent name => lIdent name
| lUnOperation is_prefix operation object => 
    lUnOperation is_prefix operation ((modify_lValue context) object)
| lError error_string => lError error_string
end.

Fixpoint modify_UrsusStatement (context: Context) (statement: UrsusStatement): UrsusStatement := 
match statement with 
(* | UExit => 
| UBreak => *)
| UFor_loop condition initialization_expression loop_expression body lice =>
    UFor_loop ((modify_rValue context) condition) ((modify_UrsusStatement context) initialization_expression) ((modify_UrsusStatement context) loop_expression) ((modify_UrsusStatement context) body) lice
| UWhile_loop condition body lice =>
    UWhile_loop ((modify_rValue context) condition) ((modify_UrsusStatement context) body) lice
| UForeach_loop range_declaration range_expression body lice =>
    UForeach_loop range_declaration ((modify_rValue context) range_expression) ((modify_UrsusStatement context) body) lice
| UIf_Then cond true_body cond_lice lice_then =>
    UIf_Then ((modify_rValue context) cond) ((modify_UrsusStatement context) true_body) cond_lice lice_then
| UIf_Then_Else cond true_body false_body cond_lice lice_then lice_else =>
    UIf_Then_Else ((modify_rValue context) cond) ((modify_UrsusStatement context) true_body) ((modify_UrsusStatement context) false_body) cond_lice lice_then lice_else
(* | UAloneValue value => *)
| UDefaultVarDeclaration objects =>
    UDefaultVarDeclaration (map (fun object => let '(ident, type):= object in (ident, (modify_rValue context) type)) objects)
| UVarDeclaration objects(*: list (lValue * rValue)*) value (*: rValue*) =>
    UVarDeclaration (map (fun object => let '(ident, type):= object in (ident, (modify_rValue context) type)) objects) ((modify_rValue context) value)
| UAssignment operator left' right' => 
    UAssignment operator ((modify_lValue context) left') ((modify_rValue context) right')
| UFunCall callable_object args =>
    let default_case := 
        UFunCall ((modify_lValue context) callable_object) (map (modify_rValue context) args)
    in
    match callable_object with 
    | lField (lFunCall (lField _ inner_name) args') member => 
        if isInList inner_name (storage_mapper_list context)
        then 
            match member with 
            | "set" =>
                let member := "svm_set" 
                in
                UFunCall (lField (lIdent inner_name) member) (map (modify_rValue context) args)
            | "update" =>
                let member := "svm_update" 
                in
                UFunCall (lField (lIdent inner_name) member) (map (modify_rValue context) args)
            | _ => 
            default_case
            end
        else
            default_case
    | lField (lFunCall (lIdent inner_name) args') member => 
        if isInList inner_name (storage_mapper_list context)
        then 
            match member with 
            | "set" =>
                let member := "svm_set" 
                in
                UFunCall (lField (lIdent inner_name) member) (map (modify_rValue context) args)
            | "update" =>
                let member := "svm_update" 
                in
                UFunCall (lField (lIdent inner_name) member) (map (modify_rValue context) args)
            | _ => 
            default_case
            end
        else
            default_case
    | _ =>
        default_case
    end
    (* UFunCall ((modify_lValue context) callable_object) (map (modify_rValue context) args) *)
| USendStatement contract address function_name args meta_data =>
    USendStatement contract address function_name (map (modify_rValue context) args) (map (fun meta_val => let '(meta, val) := meta_val in (meta, (modify_rValue context) val)) meta_data)
(* | UError error_string =>  *)
| UBlock statements => 
    let handled_statements := 
        fold_left
        (fun acc el => 
            match el with 
            | UFunCall (lIdent "require") args =>
                match args with 
                | arg1 :: arg2 :: nil =>
                    let require_statement := 
                        UFunCall (lIdent "require") [rIdent "require_arg1"; rIdent "require_arg2"]
                    in
                    let var1_declaration := 
                        UVarDeclaration [(lIdent "require_arg1", rTypeIdent "bool")] ((modify_rValue context) arg1)
                    in
                    let var2_declaration := 
                        UVarDeclaration [(lIdent "require_arg2", rTypeIdent "string")] ((modify_rValue context) arg2)
                    in
                    require_statement::var2_declaration::var1_declaration::acc
                | _ => ((modify_UrsusStatement context) el) :: acc
                end
            | _ => ((modify_UrsusStatement context) el) :: acc
            end
        )
        (statements)
        nil
    in
    UBlock (rev' handled_statements)
| st => st
end
.

Fixpoint localState_types_search (statement: UrsusStatement): list rValue := 
match statement with
| UFor_loop condition initialization_expression loop_expression body lice =>
    localState_types_search body
| UWhile_loop condition body lice =>
    localState_types_search body
| UForeach_loop range_declaration range_expression body lice =>
    localState_types_search body
| UIf_Then cond true_body cond_lice lice_then =>
    localState_types_search true_body
| UIf_Then_Else cond true_body false_body cond_lice lice_then lice_else =>
    app
    (localState_types_search true_body)
    (localState_types_search false_body)
| UDefaultVarDeclaration objects =>
    map snd objects
| UVarDeclaration objects(*: list (lValue * rValue)*) value (*: rValue*) =>
    map snd objects
| UAssignment operator left' right' => 
    nil
| UFunCall callable_object args =>
    nil
| USendStatement contract address function_name args meta_data =>
    nil
| UBlock statements => 
    fold_left
    (fun acc el =>
        app
        acc
        (localState_types_search el)
        )
    statements
    nil
| st => nil
end
.
Fixpoint get_funCall_list_Ursus (statement: UrsusStatement): list string := 
let fix get_funCall_list_rValue (object: rValue): list string := 
match object with 
| rSliceMod type => nil
| rCond cond true_val false_val => 
    app (app (get_funCall_list_rValue cond) (get_funCall_list_rValue true_val)) (get_funCall_list_rValue false_val)
| rIdent name => nil
| rLiteral literal' kind subdenomination => nil
| rTypeIdent type => nil
| rBinOperation operation left' right' => 
    app (get_funCall_list_rValue left') (get_funCall_list_rValue right')
| rUnOperation is_prefix operation object => 
    get_funCall_list_rValue object
| rField object member => 
    member::(get_funCall_list_rValue object)
| rIndex object index => 
    app (get_funCall_list_rValue object) (get_funCall_list_rValue index)
| rTuple objects => 
    fold_left
    (
        fun acc el =>
        app acc (get_funCall_list_rValue el)
    )
    objects
    nil
| rFunCall callable_object args kind => 
    let args_list := 
        fold_left
        (
            fun acc el =>
                app acc (get_funCall_list_rValue el)
        )
        args
        nil
    in
    match callable_object with 
    | rField inner member =>
        app [member] (app (get_funCall_list_rValue inner) (args_list))
    | _=> app (get_funCall_list_rValue callable_object) args_list
    end
| rReferenceMod expr => nil
| rError error_string => nil
| _ => nil

end
in
let fix get_funCall_list_lValue (object: lValue): list string := 
match object with
| lField object member => get_funCall_list_lValue object
| lIndex object index => app (get_funCall_list_lValue object)(get_funCall_list_rValue index)
| lTuple objects => 
    fold_left
    (
        fun acc el =>
        app acc (get_funCall_list_lValue el)
    )
    objects
    nil
| lFunCall callable_object args => 
    let args_list := 
        fold_left
        (
            fun acc el =>
                app acc (get_funCall_list_rValue el)
        )
        args
        nil
    in
    match callable_object with 
    | lIdent ident => [ident]
    | lField (inner) member => app (app (get_funCall_list_lValue inner) (member :: nil)) args_list
    | _ => app (get_funCall_list_lValue callable_object) args_list
    end

| lIdent name => nil
| lUnOperation is_prefix operation object => 
    get_funCall_list_lValue object
| lError error_string => nil
end
in
match statement with 
| UFor_loop condition initialization_expression loop_expression body lice => 
    app (get_funCall_list_rValue condition)
    ((app (get_funCall_list_Ursus initialization_expression)
        (app(get_funCall_list_Ursus loop_expression)
        (get_funCall_list_Ursus body))))
| UWhile_loop condition body lice => 
    app (get_funCall_list_rValue condition) (get_funCall_list_Ursus body)
| UForeach_loop range_declaration range_expression body lice => 
    (get_funCall_list_Ursus body)
| UIf_Then cond true_body cond_lice lice_then => 
    app (get_funCall_list_rValue cond) (get_funCall_list_Ursus true_body)
| UIf_Then_Else cond true_body false_body cond_lice lice_then lice_else => 
    app (get_funCall_list_rValue cond) (app (get_funCall_list_Ursus true_body)(get_funCall_list_Ursus false_body))
| UDefaultVarDeclaration objects => nil
| UVarDeclaration objects(*: list (lValue * rValue)*) value (*: rValue*) => 
    get_funCall_list_rValue value
| UAssignment operator left' right' => 
    get_funCall_list_rValue right'
| UFunCall callable_object args => 
    app
    (match callable_object with 
    | lField inner member => 
        member:: (get_funCall_list_lValue inner)
    | lIdent ident => [ident]
    | _ => (get_funCall_list_lValue callable_object)
    end)
    (let args_list := 
    fold_left
    (
        fun acc el =>
            app acc (get_funCall_list_rValue el)
    )
    args
    nil
    in
    args_list)
| USendStatement contract address function_name args meta_data => 
    (let args_list := 
    fold_left
    (
        fun acc el =>
            app acc (get_funCall_list_rValue el)
    )
    args
    nil
    in
    args_list)
| UBlock statements =>  
    fold_left
    (
        fun acc el =>
            app acc (get_funCall_list_Ursus el)
    )
    statements
    nil
| st => nil
end
.
Definition File2UrsusFile (rust_ast: json): string := 
    let attr_json : list json := 
        match (rust_ast --> "attrs"?) with | json_list l => l | _ => nil end 
    in
    let file_items_json : list json := 
        match (rust_ast --> "items"?) with | json_list l => l | _ => nil end 
    in
    let header :=
    (
        \n"Require Import UrsusEnvironment.Rust.current.Environment." ++
        \n"Require Import UrsusContractCreator.BaseContracts.MultiversxContract." ++
        \n"Require Import Containers."
    )
    in
    let import_dirs: list string := 
        let filtered := filter (fun item => match item with | json_map (mapkv "macro" _ _) => true | _ => false end) file_items_json 
        in
        map 
        (fun item => 
            ("import")
            )
        filtered
    in
    let contract_consts : list (string * rValue * rValue) := 
        let filtered := filter (fun item => match item with | json_map (mapkv "const" _ _) => true | _ => false end) file_items_json 
        in
        map 
        (fun item => 
            (
                ((item --> "const"?) --> "ident"!), 
                (fst (RustASTMultiverseX2rValue (Json2RustASTMultiverseX ((item --> "const"?) --> "ty"?)))),
                (fst (RustASTMultiverseX2rValue (Json2RustASTMultiverseX ((item --> "const"?) --> "expr"?))))
            )
            )
        filtered
    in
    let send_to_list : list string := nil 
    in
    let type_def_list: list (string * 
                            (list (string * string))) := nil 
    in
    let contract_functions (*: list (string * list string)*) := 
        let filtered_trait := filter (fun item => match item with | json_map (mapkv "trait" _ _) => true | _ => false end) file_items_json 
        in
        let group_of_funcs_json := map (fun item => (item --> "trait"?)) filtered_trait 
        in
        String.concat 
        \n""
        (map
        (fun trait => 
            let trait_name := (trait-->"ident"!) in
            let vis := (trait-->"vis"!) in
            let trait_attrs := json_pprint (trait-->"attrs"?) in
            let function_jsons := 
                match (trait --> "items"?) with 
                | json_list l => 
                    map (fun item => (item --> "fn"?)) l 
                | _ => nil 
                end 
            in
            let functions := 
                let functions_records_and_calls: list (Rust_fn * list string) := 
                    map 
                    (
                        fun function_json => 
                            let name := (function_json --> "ident"!) 
                            in
                            let fn_attrs := 
                                match (function_json --> "attrs"?) with 
                                | json_list attrs =>
                                    map
                                    (
                                        fun attr =>
                                            let meta := attr --> "meta"? 
                                            in
                                            RustASTMultiverseX2rValue (Json2RustASTMultiverseX (meta))
                                    )
                                    attrs
                                | _ => nil
                                end
                            in
                            let args := 
                                let jsons := match (function_json --> "inputs"?) with | json_list l => l | _ => nil end
                                in
                                let handled_json_arg: list (string * rValue) := 
                                    map 
                                    (
                                        fun json => 
                                        match json with 
                                        | json_map (mapkv "receiver" (json_map (mapkv "ref" (json_data is_ref) (mapkv "ty" ty_json _))) _ ) =>
                                            ("", fst (RustASTMultiverseX2rValue (Json2RustASTMultiverseX ty_json)))
                                        | json_map (mapkv "typed" typed _) =>
                                            let name := (((typed --> "pat"?) --> "ident"?) --> "ident"!) 
                                            in
                                            let type := fst (RustASTMultiverseX2rValue (Json2RustASTMultiverseX (typed --> "ty"?))) 
                                            in
                                            (name, type)
                                        | _ => ("(* haven't recognized yet *)", rError "haven't recognized yet")
                                        end
                                    ) 
                                    jsons
                                in
                                let handled_json_arg := 
                                    filter
                                    (fun name_type =>
                                        let '(name, type) := name_type 
                                        in
                                        match type with 
                                        | rError _ => false 
                                        | rIdent "Self" => false
                                        | rTypeIdent "Self" => false
                                        | _ => true
                                        end
                                    )
                                    handled_json_arg 
                                in
                                handled_json_arg
                                (* (String.concat 
                                " " 
                                (map 
                                (
                                    fun name_type =>
                                        let '(name, type) := name_type 
                                        in
                                        "("++name ++ ": " ++ (print_rValue type) ++")"
                                )
                                handled_json_arg)) *)
                            in
                            let return_type := 
                                match (function_json --> "output"?) with
                                | json_data "null" => rIdent "PhantomType"
                                | _ => 
                                    let output_json := (function_json --> "output"?) 
                                    in
                                    fst (RustASTMultiverseX2rValue (Json2RustASTMultiverseX output_json))
                                end
                            in
                            let jsons := 
                                match (function_json --> "default"?) with | json_list l => l | _ => nil end
                            in
                            let '(body, body_lice) := 
                                RustASTMultiverseX2UrsusStatement (Stmnts (map (fun js => (Json2RustASTMultiverseX js))jsons) )
                            in
                            let is_storage_mapper := 
                                fold_left 
                                (fun acc el => 
                                    match el with 
                                    | (rFunCall (rIdent "storage_mapper") _ _, _) => true
                                    | _ => acc
                                    end)
                                fn_attrs
                                false
                            in
                            (Build_Rust_fn name (map fst fn_attrs) args return_type (body, body_lice), get_funCall_list_Ursus body)
                            
                    )
                    function_jsons
                in
                map 
                fst
                (sort 
                 
                (fun fn1_and_calls fn2_and_calls =>
                    let '(func1, _) := fn1_and_calls 
                    in
                    let '(_, calls2) := fn2_and_calls 
                    in
                    let fn1_name := name func1 
                    in
                    isInList fn1_name calls2
                )
                functions_records_and_calls)
                (* (rev' functions) *)
            in
            let list_of_storage_mappers := 
                map 
                name
                (filter
                (fun function =>
                    let is_storage_mapper := 
                        fold_left 
                        (fun acc el => 
                            match el with 
                            | rFunCall (rIdent "storage_mapper") _ _ => true
                            | _ => acc
                            end)
                        (attrs function)
                        false
                    in
                    is_storage_mapper
                )
                functions)
            in
            let list_of_storage_mappers_and_type: list string := 
            (
                map
                (fun function =>
                    (name function) ++ " ( "++ String.concat " -> "(map print_rValue (app (map snd (args function)) [(return_type function)])) ++ ")"
                    (* caller_address (SingleValueMapper address) *)
                )
                (filter
                (fun function =>
                    let fn_attrs := attrs function 
                    in
                    fold_left 
                    (fun acc el => 
                        match el with 
                        | rFunCall (rIdent "storage_mapper") _ _ => true
                        | _ => acc
                        end)
                    fn_attrs
                    false
                    )
                functions)
            )
            in
            let handled_functions := 
            map
            (fun function =>
                let context := 
                    Build_Context list_of_storage_mappers id
                in
                let (body, body_lice) := (body function) 
                in
                (Build_Rust_fn (name function) (attrs function) (args function) (return_type function) (((modify_UrsusStatement context) body), body_lice))
            )
            functions
            in
            let localState_types_string: list string := 
                let localState_types := 
                    fold_left
                    (fun acc function =>
                        let (body, body_lice) := (body function) 
                        in
                        app
                        (map snd (args function))
                        (app 
                        ((return_type function)::acc)
                        (localState_types_search body))
                    )
                    functions
                    nil
                in
                (drop_duplicate 
                (map 
                print_rValue 
                ((rFunCall (rIdent "Option") [rIdent "unit"] "")::(rIdent "unit")::localState_types)) 
                String.eqb)

            in
            \n"(* #[language = Rust] *)" ++
            \n"#[translation = off]" ++
            \n"Contract "++trait_name++" ;" ++
            \n"Sends To (* *) ; " ++
            \n"Inherits MultiversxBaseContract ; " ++
            \n"Types ;" ++
            \n"Constants "++
            (String.concat 
            ""
                (
                map
                (fun name_type_value =>
                    let '(name, type ,value) := name_type_value 
                    in
                    \n"Definition " ++ name ++ ":" ++ (print_rValue type) ++ " := " ++ (print_rValue value)
                )
                contract_consts
                )
            )
            ++" ;" ++
            \n"StorageMappers" ++
            \n"    " ++ (String.concat \n"    " list_of_storage_mappers_and_type) ++ \n";" ++
            \n"Record Contract := {"++
            \n"}."++
            \n""++
            \n"SetUrsusOptions."++
            \n"Unset Ursus Extraction."++
            \n""++
            \n"UseLocal Definition _ := [" ++
            \n"    " ++ (String.concat (";" ++ \n"    ") localState_types_string) ++
            \n"]."++
            (*\n"(* attributes of trait is" ++ trait_attrs ++ " *)" ++*)
            (print_rust_functions handled_functions) ++
            \n""++
            \n"EndContract." ++
            \n""++
            \n"GenerateLocalState 0 "++trait_name++"." ++
            \n"GenerateLocalState "++trait_name++"."
            
            
        ) 
        group_of_funcs_json)
        
    in
    header ++
    contract_functions
.

