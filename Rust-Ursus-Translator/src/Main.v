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
Require Import Io.All.
Require Import System.All.
Import C.Notations.
Require Import CoqJson.Parser.
Require Import ListString.All.
Require Import ProgramScheme.

Definition translator (argv : list LString.t): 
    C.t System.effect Datatypes.unit :=
match argv with
| [ _ ; path_to_ast] =>
    let! ast_LString := System.read_file path_to_ast in
    match ast_LString with
    | Some ast_LString =>
        let '(ast_LString, ast_depth) := reconfigure ast_LString nil nil 0 0 in 
        let ast_LString :=  t2strPlusRev' ast_LString "" in 
        let ast_term := pars' ast_LString  ast_depth ast_depth in 
        let file : string := 
            File2UrsusFile ast_term
        in
        System.log (LString.s file) 
    | _ => System.log  (LString.s "Cannot read the files.1"%string)
    end
| _ => System.log (LString.s "Expected a parameter.")
end.


Definition translate := Extraction.launch translator.
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "main" translate.
