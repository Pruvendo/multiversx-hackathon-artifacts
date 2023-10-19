
Require Import UrsusEnvironment.Rust.current.Environment.
Require Import UrsusContractCreator.BaseContracts.MultiversxContract.
Require Import Containers.
(* #[language = Rust] *)
#[translation = off]
Contract Adder ;
Sends To (* *) ; 
Inherits MultiversxBaseContract ; 
Types ;
Constants  ;
StorageMappers
    sum ( SingleValueMapper(BigUint))
;
Record Contract := {
}.

SetUrsusOptions.
Unset Ursus Extraction.

UseLocal Definition _ := [
    Option(unit);
    unit;
    BigUint;
    PhantomType;
    SingleValueMapper(BigUint)
].
(* attributes of trait is[{"style": "outer","meta": {"name_value": {"path": {"segments": [{"ident": "doc"}]},"value": {"lit": {"str": "\ One of the simplest smart contracts possible,\"}}}}},{"style": "outer","meta": {"name_value": {"path": {"segments": [{"ident": "doc"}]},"value": {"lit": {"str": "\ it holds a single variable in storage, which anyone can increment.\"}}}}},{"style": "outer","meta": {"path": {"segments": [{"ident": "multiversx_sc"},{"ident": "contract"}]}}}] *)
(* Ursus Definition sum : UExpression (SingleValueMapper(BigUint)) false. 
return. Defined. Sync. *)

Ursus Definition add (value: BigUint): UExpression (PhantomType) true.
{
    :://   sum->svm_update(fun λsum=> // (λsum:=(λsum+{value})) // ) |.
}
return. Defined. Sync.

Ursus Definition init (initial_value: BigUint): UExpression (PhantomType) false.
{
    :://   sum->svm_set(initial_value) |.
}
return. Defined. Sync.

EndContract.

GenerateLocalState 0 Adder.
GenerateLocalState Adder.