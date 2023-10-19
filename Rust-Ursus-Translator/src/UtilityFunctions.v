Require Import Coq.Lists.List.
Require Import Io.All.
Require Import System.All.
Require Import ListString.All.
Require Import String.
Require CoqJson.KeyMaps.
Require Import Coq.Bool.Bool.
Open Scope string_scope.
Require Import Bool.

Require Import CoqJson.Json.

Import ListNotations.
Import C.Notations.
Import JsonNotations.

Local Open Scope json_scope.
Delimit Scope json_scope with json.
Require Import Ascii.

Require Import Coq.Init.Nat.

Fixpoint isInList(arg: string)(ls: list string): bool :=
match ls with 
| head :: body => if arg =? head 
                    then true 
                    else isInList(arg)(body)
| nil => false
end  
.

Notation "'\n' a" := (String "010"%char a)(at level 0).


Definition getJSON(o: option json): json :=
  match o with
    | Some a => a
    | None => { }
  end.

Definition getString(o: option json): string :=
  match getJSON(o) with
  | json_data s => s
  | _ => ""
  end.

Definition getString'(j : json): string := 
match j with 
| json_data s => s
| _ => ""
end  
.
Definition getMap(j: json) := 
match j with 
| json_map m => m
| _ => empty
end  
.



Fixpoint t2str (t : LString.t): string :=
match t with 
| tail :: body => (String tail "")++t2str(body)
| nil => ""
end    
.

Definition enumerate {A}(l:list A): list (nat*A):=
  let fix enumerate' {A}(len: nat)(l:list A): list (nat*A):=
    let n:= (List.length l)-1 in 
    match l with 
    | tail :: body => pair(len- n)(tail)::enumerate'(len)(body)
    | nil => nil
    end
  in
enumerate'((List.length l)-1)l 
.

(* Compute enumerate ["";"1"]. *)

Fixpoint handle_struct_name (name :string) : string :=
match name with  
| String "."%char tail => "_ι_" ++ (handle_struct_name tail) 
| String head tail => String head (handle_struct_name tail)
| EmptyString => EmptyString
end
.

Definition strOrNot(fl:bool)(str: string): string :=  if fl then str else "".

Fixpoint replace'(old: string)(new: string) (s:string) (acc: string):=
match s with 
| String head body => let lenO := length old in 
                      let lenA := length acc in
                      if old =? substring 0 lenO acc
                      then replace' (old)(new)(body)(String (head)(new ++ substring lenO (lenA) acc))
                      else (replace' (old) (new) (body) (String (head) acc))
| EmptyString => let lenO := length old in 
                  let lenA := length acc in
                  if old =? substring (0) lenO acc
                  then  new ++ substring (lenO)(lenA) acc 
                  else  acc
end  
.

Definition replace(old: string)(new: string) (s:string) := 
  let out := string_rev (replace' (string_rev old) (string_rev new) s "") in out.

Definition replace_or_nothing(old: string)(new:string)(s: string):=
  let out := string_rev (replace' (string_rev old) (string_rev new) s "") in
  if out =? s  then "" else out
.


Definition not (b: bool):=
match b with
| true => false
| false => true
end  
.
Fixpoint list_to_map(l: list (string * json)): key_map := 
match l with 
| tail :: body => mapkv (fst tail) (snd tail) (list_to_map body)
| nil => empty
end.
Fixpoint replace_few_things (old: list string) (new: list string) (s:string): string :=
match old, new  with 
| tail' :: body', tail'' :: body'' => let newS := replace tail' tail'' s in replace_few_things (body') (body'') (newS)
| nil,nil => s
| _, _ => ""
end
.

Fixpoint replaceWith(oldAndNew: list(string*string))(s:string):string :=
match oldAndNew with 
| tail :: body => let newS:= replace (fst tail)(snd tail) s in replaceWith body newS
| nil => s
end
.

Definition isInStr (it: string)(s: string): bool := not(s =? replace(it)("")(s)).

Fixpoint split_string' (s: string) (p: string) n : list string :=
match n with
| O => []
| S n' => 
if (string_dec s "") then [] else
if (string_dec p "") then (substring 0 1 s)::
                          (split_string' (substring 1 ((String.length s) - 1) s) p n') else
let i := index 0 p s in
match i with
| None => [s]
| Some k => let ss := substring 0 k s in
            let a  := k + (String.length p) in
            let s' := substring a ((String.length s) - a) s in
            ss::(split_string' s' p n')
end
end.

Definition split_string s p := split_string' s p (String.length s). 

Definition simpleType :=  replaceWith [("string","string");("uint256","uint256");("uint128","uint128");("uint128","uint128");
("uint64","uint64");("uint32","uint32");("uint16","uint16");("uint8","uint8");
("uint","uint");("boolean","bool");("bool","boolean");("cell","TvmCell");("TvmCell","TvmCell");("TvmSlice","TvmSlice"); 
(* ("bytes4","(XList XUInteger8)"); *)
("bytes","bytes");("TvmBuilder","TvmBuilder")].


Definition xtype(resolve_name:bool)(type:string):string :=
let type := replaceWith [("type(","(");("tuple()", "");("("," ( "); (")"," ) "); (",", " , ");(".", "_ι_");(",", "**"); ("  ", " ") ] type in
let splittedType := split_string type " " in
let fix handle_splittedType (typeSeq: list string)(context_stack: list string)(acc: string) := 
match typeSeq with 
| head :: body => 
      match head with
      | "contract" => handle_splittedType(body)("contract"::context_stack)(acc)
      | "struct" => handle_splittedType(body)("struct"::context_stack)(acc)
      | "library" => handle_splittedType(body)("library"::context_stack)(acc)
      | "=>" => handle_splittedType(body)(context_stack)(acc ++ " )(" )
      | "mapping" => handle_splittedType(body)(context_stack)(acc ++ " mapping " )
      | "optional" => handle_splittedType(body)(context_stack)(acc ++ " optional " )
      | "int_const" => handle_splittedType(body)("int_const"::context_stack)(acc)
      | "(" => match context_stack with
              | "tuple" :: body' => handle_splittedType(body)(context_stack)(acc++ " " ++ head )
              | _ => handle_splittedType(body)(context_stack)(acc ++ " "++ head )
              end
      | "tuple" => handle_splittedType(body)("tuple"::context_stack)(acc)
      | ")" =>  match context_stack with
                | "tuple" :: body' => handle_splittedType(body)(body')(acc ++ " "++ head )
                | _ => handle_splittedType(body)(context_stack)(acc ++ " "++ head )
                end
      | "**" => handle_splittedType(body)(context_stack)(acc ++ " ** " ++ " ")        
      | _ =>  let isArray := isInStr "[]" head in 
              let head := replaceWith [("[]","")] head in 
              (* fixme double unnecessary replace to ι  *)
              let head := 
                last (split_string head "_ι_") head in
              match context_stack with
                  | "int_const" :: body' => handle_splittedType(body)(body')(acc ++ " " ++ head)
                  | "contract"  :: body' => handle_splittedType(body)(body')(acc ++ "("++ (if resolve_name then "_ResolveName" ++ " "++ """" ++ head ++  """" else (head++"LRecord")) ++ (strOrNot isArray "[]") ++ ")")
                  | "struct"    :: body' => handle_splittedType(body)(body')(acc ++ "("++ (if resolve_name then "_ResolveName" ++ " "++ """" ++ head ++  """" else (head++"LRecord")) ++ (strOrNot isArray "[]") ++ ")")
                  | "library"   :: body' => handle_splittedType(body)(body')(acc ++ "("++ (if resolve_name then "_ResolveName" ++ " "++ """" ++ head ++  """" else (head++"LRecord")) ++ (strOrNot isArray "[]") ++ ")")
                  | _ => 
                      let head := simpleType head in
                      handle_splittedType(body)(context_stack)(acc ++ " " ++ head++(strOrNot isArray "[]"))
                  end
      end
| nil => acc 
(* ++ ""++String.concat "," context_stack ++ "" *)
end
in 
handle_splittedType splittedType nil ""  
.


Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := (natToDigit (n mod 10)) ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

Definition drop_duplicate{A}(ls : list A)(eq: A -> A -> bool) :list A:=
  let fix drop_dupl (ls : list A)(eq: A -> A -> bool)(acc:list A) :=
  let fix isInList (a: A)(l: list A):bool := 
    match l with 
    | tail' :: body' =>  if eq tail' a then true else isInList a body'
    | nil => false
    end
  in
  match ls with
  | tail :: body => 
    if isInList tail acc 
    then drop_dupl body eq acc 
    else drop_dupl body eq (app acc [tail])
  | nil => acc
  end    
  in
drop_dupl ls eq nil
.

Notation "b '-->' something '!'  " := (getString(json_get(inl something )(b))) (at level 500, left associativity).
Notation "b '-->' something '?'  " := (getJSON(json_get(inl something )(b))) (at level 500, left associativity).
Notation "b '-->' something '??'  " := ((json_get(inl something )(b))) (at level 500, left associativity).


Arguments app {_} (l l')%list_scope.

Fixpoint get_json_with_nodetype(nodetype:string)(j: json): list json :=
let fix iter' m :=
    match m with 
    | empty => []
    | mapkv k v m' => app (get_json_with_nodetype nodetype v) (iter' m')
    end 
in    
match j with
  | json_data s => []
  | json_list l => fold_left app (map (get_json_with_nodetype nodetype) l) nil 
  | json_map m => 
                match( j --> "nodeType"!) with
                | s => 
                    if s =? nodetype 
                    then [j]
                    else iter' m
                end
end
.

(* MAIN PART*)

(* https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html *)
Fixpoint insert{A} (leb: A -> A -> bool) (i : A) (l : list A) :=
  match l with
  | [] => [i]
  | h :: t => if (leb i h) then i :: h :: t else h :: insert leb i t
  end.
Fixpoint sort{A} (leb: A -> A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => insert leb h (sort leb t)
  end.