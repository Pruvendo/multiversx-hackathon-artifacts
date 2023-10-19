Require Import Coq.Program.Basics. 
From mathcomp Require Import tuple.
Require Import Coq.Strings.String. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Program.Equality.
Require Import NArith.

Require Import FinProof.Common. 
Require Import FinProof.CommonInstances.
Require Import FinProof.EpsilonMonad.
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.MonadTransformers21. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Lib.ListsNat.

From UMLang Require Import UrsusLib UrsusCoercions.

Require Import UrsusStdLib.Rust.All.

Require Import Rust.Types.

Set Typeclasses Depth 100.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope urust_scope.
Local Open Scope string_scope.

Class VMStateClass (Ledger LedgerMainState LedgerLocalState LedgerMessagesAndEvents: Type) := 
{
	VMLedgerClass :> LedgerClass XBool Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents;
	PersistentContractDataEmbedded :> EmbeddedType (field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_MainState) PersistentContractDataLRecord
}.

Section tvmFuncDef.

Context {Ledger LedgerMainState LedgerLocalState LedgerMessagesAndEvents  : Type}.
(* Context `{ledgerClass: LedgerClass XBool Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents GlobalParamsLRecord OutgoingMessageParamsLRecord}. *)
Context `{vmStateClass: VMStateClass Ledger LedgerMainState LedgerLocalState LedgerMessagesAndEvents}.
Context {Lifr: listInfiniteFunRec_gen XList}.

#[local]
Notation UExpression := (@UExpressionL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents VMLedgerClass) .
#[local]
Notation ULValue := (@ULValueL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents VMLedgerClass) .
#[local]
Notation URValue := (@URValueL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents VMLedgerClass) .
#[local]
Notation wrapULExpression := (@wrapULExpressionL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents VMLedgerClass _ _ _ _ ).
#[local]
Notation wrapURExpression := (@wrapURExpressionL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents VMLedgerClass _ _ _ ).
#[local]
Notation ursus_call_with_args := (@ursus_call_with_argsL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents VMLedgerClass _ _  ).

Section Random.

Inductive RandomnessSource := Build_RS.
Definition new_rs : URValue RandomnessSource false := URScalar Build_RS.

Definition XRandomEmbedded: EmbeddedType (field_type Ledger_VMState) u32.
	rewrite <- isoVMState.
	exact (VMStateLEmbeddedType VMState_ι_random).
Defined.

Definition nextu32' (rs : RandomnessSource): UExpression u32 false.
	refine (// { ULState Ledger_VMState XRandomEmbedded } := 
		{_: URValue u32 false};
			return_ {_} //).
	1-2: replace false with (false || false); auto;
		 refine (urvalue_bind _ (fun old_rnd => _));
		 [eapply (URState); refine XRandomEmbedded|].

	(* source: https://en.wikipedia.org/wiki/Linear_congruential_generator#Parameters_in_common_use *)
	1-2: set (MOD := @Build_XUBInteger 32 (N.shiftl 1 32));
		 set (A := @Build_XUBInteger 32 1664525%N);
		 set (C := @Build_XUBInteger 32 1013904223%N);
		 refine (URScalar (xIntMod (xIntPlus (xIntMult old_rnd A) C) MOD)).
Defined.

Ltac add_rs_rvalue next b _rs := 
	refine (// return_ {_} //);
	replace b with (b || false); [|destruct b; auto];
	refine (urvalue_bind _rs (fun rs =>
	wrapURExpression (ursus_call_with_args λ1 next (URScalar rs)))).

Definition nextu32 {b} (_rs : URValue RandomnessSource b) : UExpression u32 b.
	add_rs_rvalue nextu32' b _rs.
Defined.

Definition nextu32_inrange_templ (rs: RandomnessSource) 
								 (mn: u32)
                           		 (mx: u32) 
						: UExpression u32 false.
	refine (// return_ {_} //).
	replace false with (false || false); [|auto].
	refine (urvalue_bind _ (fun rnd => _)).
	refine (wrapURExpression (ursus_call_with_args λ1 nextu32' (URScalar rs))).
	refine (URScalar (xIntPlus mn (xIntMod rnd (xIntMinus mx mn)))).
Defined.

Definition nextu32_inrange {b0 b1 b2} (_rs : URValue RandomnessSource b0)
								      (_mn: URValue u32 b1)
						   		      (_mx: URValue u32 b2) 
		: URValue u32 (b0 || (b1 || b2)).
	replace b2 with (b2 || false); [|destruct b2; auto].
	refine (urvalue_bind _rs (fun rs =>
			urvalue_bind _mn (fun mn =>
			urvalue_bind _mx (fun mx => _)))).
	refine (wrapURExpression (ursus_call_with_args λ3 nextu32_inrange_templ (URScalar rs) mn mx)).
Defined.

Ltac next_u32_and_trunc rs mn mx:=
	replace false with (false || false); auto;
	refine (urvalue_bind _ (fun rnd => URScalar (Build_XUBInteger (uint2N rnd))));
	replace false with (false || (false || false)); auto;
	refine (wrapURExpression (ursus_call_with_args λ3 nextu32_inrange_templ (URScalar rs) (convert_uint _ mn) (convert_uint _ mx))).

Definition nextu8' (rs: RandomnessSource): UExpression u8 false.
	refine (// return_ {_} //).
	unshelve next_u32_and_trunc rs 0%N (N.shiftl 1 8).
	1-2: refine 8%N. 1-2: compute; congruence.
Defined.

Definition nextu8 {b} (_rs : URValue RandomnessSource b) : UExpression u8 b.
	add_rs_rvalue nextu8' b _rs.
Defined.

Definition nextu8_inrange {b0 b1 b2} (_rs: URValue RandomnessSource b0)
								  (_mn: URValue u8 b1)
						          (_mx: URValue u8 b2) 
		: URValue u8 (b0 || (b1 || b2)).
	replace b2 with (b2 || false); [|destruct b2; auto].
	refine (urvalue_bind _rs (fun rs =>
			urvalue_bind _mn (fun mn =>
			urvalue_bind _mx (fun mx => _)))).
	next_u32_and_trunc rs mn mx.
	1-2: compute; congruence.
Defined.

Definition nextu16' (rs: RandomnessSource): UExpression u16 false.
	refine (// return_ {_} //).
	unshelve next_u32_and_trunc rs 0%N (N.shiftl 1 16).
	1-2: refine 16%N. 1-2: compute; congruence.
Defined.

Definition nextu16 {b} (_rs : URValue RandomnessSource b) : UExpression u16 b.
	add_rs_rvalue nextu16' b _rs.
Defined.

Definition nextu16_inrange {b0 b1 b2} (_rs: URValue RandomnessSource b0)
								      (_mn: URValue u16 b1)
						              (_mx: URValue u16 b2) 
		: URValue u16 (b0 || (b1 || b2)).
	replace b2 with (b2 || false); [|destruct b2; auto].
	refine (urvalue_bind _rs (fun rs =>
			urvalue_bind _mn (fun mn =>
			urvalue_bind _mx (fun mx => _)))).
	next_u32_and_trunc rs mn mx.
	1-2: compute; congruence.
Defined.

Definition nextu64' (rs: RandomnessSource): UExpression u64 false.
refine (//return_ {_}//).
replace false with (false || (false || false)); auto.
refine (urvalue_bind _ (fun rnd1 => 
		urvalue_bind _ (fun rnd2 => _))).
1-2: refine (wrapURExpression (ursus_call_with_args λ1 nextu32' (URScalar rs))).
refine (let rnd1_64 : u64 := convert_uint _ rnd1 in _).
refine (let rnd2_64 : u64 := convert_uint _ rnd2 in _).
refine (URScalar (xIntPlus (xIntBitOpLeft rnd1_64 32%N) rnd2_64 )).
Unshelve. 1-2: compute; congruence.
Defined.

Definition nextu64 {b} (_rs : URValue RandomnessSource b) : UExpression u64 b.
	add_rs_rvalue nextu64' b _rs.
Defined.

Definition nextu64_inrange {b0 b1 b2} (_rs: URValue RandomnessSource b0)
								   	  (_mn: URValue u64 b1)
						   		   	  (_mx: URValue u64 b2) 
		: URValue u64 (b0 || (b1 || b2)).
	replace b2 with (b2 || (false || false)); [|destruct b2; auto].
	refine (urvalue_bind _rs (fun rs =>
			urvalue_bind _mn (fun mn =>
			urvalue_bind _mx (fun mx => 
			urvalue_bind _   (fun rnd => _))))).
	refine (wrapURExpression (ursus_call_with_args λ1 nextu64' (URScalar rs))).
	refine (URScalar (xIntPlus mn (xIntMod rnd (xIntMinus mx mn)))).
Defined.

Definition nextu8_urvalue {b} (rs : URValue RandomnessSource b) : URValue u8 b.
	apply wrapURExpression.
	replace b with (false || b); auto.
	refine (ursus_call_with_args λ1 nextu8' rs).
Defined.

Definition nextu16_urvalue {b} (rs : URValue RandomnessSource b) : URValue u16 b.
	apply wrapURExpression.
	replace b with (false || b); auto.
	refine (ursus_call_with_args λ1 nextu16' rs).
Defined.

Definition nextu32_urvalue {b} (rs : URValue RandomnessSource b) : URValue u32 b.
	apply wrapURExpression.
	replace b with (false || b); auto.
	refine (ursus_call_with_args λ1 nextu32' rs).
Defined.

Definition nextu64_urvalue {b} (rs : URValue RandomnessSource b) : URValue u64 b.
	apply wrapURExpression.
	replace b with (false || b); auto.
	refine (ursus_call_with_args λ1 nextu64' rs).
Defined.

End Random.

Section TokenIdentifier.

(* TODO! *)
Definition isvalid {b} (tid: URValue EgldOrEsdtTokenIdentifier b) :
		URValue bool b.
	replace b with (b || false); [|destruct b; auto].
	refine (urvalue_bind tid (fun _ => _)).
	refine (URScalar true).
Defined.

End TokenIdentifier.

Section CallValue.

Inductive CallValue := Build_CV.
Definition new_cv : URValue CallValue false := URScalar Build_CV.

Definition egld_value' {b} (cv : URValue CallValue b): URValue BigUint b.
	replace b with (b || false); [|destruct b; auto].
	refine (urvalue_bind cv (fun _ => _)).
	assert (URValue MultivMessage false).	
	refine (URState Ledger_VMState).
	rewrite <- isoVMState. 
	refine (VMStateLEmbeddedType VMState_ι_currentInboudMessage).
	refine (urvalue_bind X (fun x => URScalar (InternalMessage_ι_value x))).
Defined.

Ltac read_msg_tokens cv b := 
	replace true with (b || true); [|destruct b; auto];
	refine (urvalue_bind cv (fun _cv => _));
	assert (X: URValue MultivMessage false);
	[refine (URState Ledger_VMState);
	rewrite <- isoVMState;
	refine (VMStateLEmbeddedType VMState_ι_currentInboudMessage)|];
	refine (urvalue_bind X (fun msg => let tokens := (InternalMessage_ι_tokens msg) in _)).

Definition all_esdt_transfers' {b} (cv : URValue CallValue b): URValue (listVector EsdtTokenPayment) b.
	replace b with (b || false); [|destruct b; auto];
	read_msg_tokens cv b. refine (URScalar (wrap _ tokens)).
Defined.

Definition multi_esdt' (n : u32) (* not URValue, type parameter! *) 
					   {b} (cv : URValue CallValue b)
		: URValue (listVector EsdtTokenPayment) true.
	read_msg_tokens cv b.
	replace (true) with (false || false || true); auto.
	eapply UR3arn; try apply URScalar.
	- refine (Common.eqb (N.of_nat (List.length tokens)) (uint2N n)).
	- refine (wrap _ tokens).
	- refine (URResult ($ (ControlError ERROR_DEFAULT))).
Defined.

Definition single_esdt' {b} (cv : URValue CallValue b): URValue EsdtTokenPayment true.
	read_msg_tokens cv b.
	replace (true) with (false || false || true); auto.
	eapply UR3arn; try apply URScalar.
	- refine (Common.eqb (List.length tokens) 1%nat).
	- refine (List.hd default tokens).
	- refine (URResult ($ (ControlError ERROR_DEFAULT))).
Defined.

Definition single_fungible_esdt' {b} (cv : URValue CallValue b): URValue (TokenIdentifier * BigUint) true.
	read_msg_tokens cv b.
	replace (true) with (false || false || true); auto.
	destruct (List.hd default tokens) as [ tid [nonce value] ].
	eapply UR3arn; try apply URScalar.
	- apply andb. 
		refine (Common.eqb (List.length tokens) 1%nat).
		refine (Common.eqb nonce 0%N).
	- refine (tid, value).
	- refine (URResult ($ (ControlError ERROR_DEFAULT))).
Defined.

Definition egld_or_single_esdt' {b} (cv : URValue CallValue b): URValue EgldOrEsdtTokenPayment true.
	read_msg_tokens cv b.
	replace (true) with (false || b || true); [|destruct b;auto].
	eapply UR3arn.
	- refine (URScalar (Common.eqb (List.length tokens) 0%nat)).
	- replace b with (b||false); [|destruct b; auto].
	  refine (urvalue_bind (egld_value' cv) (fun value => 
		URScalar (None, (Build_XUBInteger 0, value))
	  )).
	- refine (urvalue_bind (single_esdt' cv) (fun res => URScalar _)).
	  destruct res as [ tid [nonce value] ].
	  refine (Some tid, (nonce, value)).
Defined.

Definition egld_or_single_fungible_esdt' {b} (cv : URValue CallValue b): URValue (EgldOrEsdtTokenIdentifier * BigUint) true.
	read_msg_tokens cv b.
	replace (true) with (false || b || true); [|destruct b; auto].
	eapply UR3arn.
	- refine (URScalar (Common.eqb (List.length tokens) 0%nat)).
	- replace b with (b||false); [|destruct b; auto].
	  refine (urvalue_bind (egld_value' cv) (fun value => 
		URScalar (None, value)	
	  )).
	- refine (urvalue_bind (single_fungible_esdt' cv) (fun res => URScalar _)).
	  destruct res as [tid value].
	  refine (Some tid, value).
Defined.

End CallValue.

Section Blockchain.

Inductive Blockchain := Build_BC.
Definition new_bc : URValue Blockchain false := URScalar Build_BC.

Definition XTokensEmbedded: EmbeddedType (field_type Ledger_MainState) (XHMap (TokenIdentifier * u64) BigUint).
	refine (@TransEmbedded _ _ _ PersistentContractDataEmbedded _).
	refine (PersistentContractDataLEmbeddedType PersistentContractData_ι_tokens).
Defined.

Definition XBalanceEmbedded: EmbeddedType (field_type Ledger_MainState) BigUint.
	refine (@TransEmbedded _ _ _ PersistentContractDataEmbedded _).
	refine (PersistentContractDataLEmbeddedType PersistentContractData_ι_balance).
Defined.

Definition get_sc_balance' {b0 b1 b2} 
		(bc : URValue Blockchain b0)
		(token: URValue EgldOrEsdtTokenIdentifier b1)
		(_nonce: URValue u64 b2) : URValue BigUint (b0 || (b1 || b2)).
	apply (urvalue_bind bc); intros _;
	apply (urvalue_bind token); intros [tid|];
	replace b2 with (b2 || false); try apply orb_false_r; 
	apply (urvalue_bind _nonce); intros nonce.
	- assert (tokens': URValue (XHMap (TokenIdentifier * u64) BigUint) false).
	  refine (URState Ledger_MainState).
	  refine (XTokensEmbedded).
	  refine (urvalue_bind tokens' (fun tokens => _)).
	  refine (URScalar (hmapFindWithDefault (Build_XUBInteger 0)
	  	 (tid, nonce) tokens)).
	- refine (URState Ledger_MainState).	
	  refine XBalanceEmbedded.
Defined.

Definition get_block_timestamp' {b} (bc: URValue Blockchain b): URValue u64 b.
	replace b with (b || false); [|destruct b; auto].
	apply (urvalue_bind bc); intros _.
	refine (URState Ledger_VMState).
	rewrite <- isoVMState.
	refine (VMStateLEmbeddedType VMState_ι_block_timestamp).
Defined.

Definition get_block_epoch' {b} (bc: URValue Blockchain b): URValue u64 b.
	replace b with (b || false); [|destruct b; auto].
	apply (urvalue_bind bc); intros _.
	refine (URState Ledger_VMState).
	rewrite <- isoVMState.
	refine (VMStateLEmbeddedType VMState_ι_block_epoch).
Defined.

Definition get_block_round' {b} (bc: URValue Blockchain b): URValue u64 b.
	replace b with (b || false); [|destruct b; auto].
	apply (urvalue_bind bc); intros _.
	refine (URState Ledger_VMState).
	rewrite <- isoVMState.
	refine (VMStateLEmbeddedType VMState_ι_block_round).
Defined.

Definition XAddressEmbedded: EmbeddedType (field_type Ledger_MainState) address.
	refine (@TransEmbedded _ _ _ PersistentContractDataEmbedded _).
	refine (PersistentContractDataLEmbeddedType PersistentContractData_ι_address).
Defined.

Definition get_sc_address' {b} (bc: URValue Blockchain b): URValue address b.
	replace b with (b || false); [|destruct b; auto].
	apply (urvalue_bind bc); intros _.
	refine (URState Ledger_MainState).	
	refine XAddressEmbedded.
Defined.

Definition get_caller' {b} (bc: URValue Blockchain b): URValue address b.
	replace b with (b || false); [|destruct b; auto].
	apply (urvalue_bind bc); intros _.
	assert (URValue MultivMessage false).	
	refine (URState Ledger_VMState).
	rewrite <- isoVMState. 
	refine (VMStateLEmbeddedType VMState_ι_currentInboudMessage).
	refine (urvalue_bind X (fun x => URScalar (InternalMessage_ι_sender x))).
Defined.

Definition XOwnerEmbedded: EmbeddedType (field_type Ledger_MainState) address.
	refine (@TransEmbedded _ _ _ PersistentContractDataEmbedded _).
	refine (PersistentContractDataLEmbeddedType PersistentContractData_ι_owner).
Defined.

Definition owner_address {b} (bc: URValue Blockchain b): URValue address b.
	replace b with (b || false); [|destruct b; auto].
	apply (urvalue_bind bc); intros _.
	refine (URState Ledger_MainState).	
	refine XOwnerEmbedded.
Defined.

End Blockchain.

Section Send.

Inductive Send := Build_send.
Definition new_send : URValue Send false := URScalar Build_send.

Definition remove_tokens (tokenmap: XHMap (TokenIdentifier * u64) BigUint)
		(tid: TokenIdentifier) (nonce: u64) (amount : BigUint):
	XHMap (TokenIdentifier * u64) BigUint :=
xHMapAdjust (fun v => xIntMinus v amount) (tid, nonce) tokenmap.


Definition messageQueue I := XHMap address (XQueue (OutgoingMessage I)).
(*queue for transfers*)
Class DefaultMessageQueue :=
{
	defaultMessageQueue : ULValue (messageQueue IDefault)
}.

Class MessageQueue (T: Type) 
                   (* (b: bool) (m: URValue T b) *) :=
{
    messageLQ : ULValue (messageQueue T)
}.
Import ListNotations.
Definition direct' `{DefaultMessageQueue} (send: Send)
				   (dest: address)
				   (tid: EgldOrEsdtTokenIdentifier)
				   (nonce: u64)
				   (amount: BigUint):
	UExpression PhantomType false.
replace false with (false || false || false || false); auto.
apply StrictBinding.
apply IfElseExpression.
- refine (isSome tid).
- (* esdt *) refine (// {_: ULValue (XHMap (TokenIdentifier * u64) BigUint)} := {_} //).
  refine (ULState Ledger_MainState XTokensEmbedded).
  replace false with (false || false); auto.
  refine (urvalue_bind (_: URValue (XHMap (TokenIdentifier * u64) BigUint) _) (fun tokenmap => _)).
  refine (URState Ledger_MainState). refine XTokensEmbedded.
  refine (URScalar (remove_tokens 
  	tokenmap 
	(xMaybeMapDefault id tid default) 
	nonce
    amount
  )).
- (* egld *) refine (// {_} -= {amount} //).
  refine (ULState Ledger_MainState _).
  refine XBalanceEmbedded.

refine // {_ : ULValue (XQueue (OutgoingMessage IDefault))} ->  queue_push ( { _: URValue _ false } ) //. 
destruct H.
refine (ULIndex (URScalar dest) defaultMessageQueue0).
refine (urvalue_bind (get_sc_address' (URScalar Build_BC)) (fun source => _)).
apply URScalar. constructor. split.
refine dest. split.
refine source. split.
destruct tid. refine xInt0. refine amount.
destruct tid. refine ([(t, (nonce, amount))]). refine ([ ]).
Defined.

Definition direct_ulvalue `{DefaultMessageQueue} {b0 b1 b2 b3 b4} 
						  (send: URValue Send b0)
						  (addr: URValue address b1)
				   		  (tid: URValue EgldOrEsdtTokenIdentifier b2)
				   		  (nonce: URValue u64 b3)
				          (amount: URValue BigUint b4):
UExpression PhantomType (b4 || b3 || b2 || b1 || b0) :=
	(wrapULExpression (ursus_call_with_args λ5 direct' send addr tid nonce amount)).

End Send.

(* TODO: this is copy/paste from solidity part, 
we need to somehow extract to common stuff like this *)
Section AddressEqb.

Definition addr_std_ι_workchain_id_right {b} (x: URValue address b): URValue XInteger b :=
    \\  ({x} ^^ {add_std_ι_workchain_id}) \\ : _.

Definition addr_std_ι_workchain_id_left (x: ULValue address): ULValue XInteger :=
    // {x} ^^ {add_std_ι_workchain_id} // : _.   

Definition addr_std_ι_address_right {b} (x: URValue address b): URValue u256 b :=
    \\ {x} ^^ {add_std_ι_address} \\ : _.

Definition addr_std_ι_address_left (x: ULValue address): ULValue u256 :=
    // {x} ^^ {add_std_ι_address} // : _. 

Require Import ZArith.
Local Open Scope Z_scope.
Arguments BinaryLogicalOperations {_} {_} {_} {_} {_} {_} _ _ _.
Arguments ueqb {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} _ {_} _.
Arguments ultb {_} {_} {_} {_} {_} {_} {_} {_} {_} _ {_} _.
Arguments uand {_} {_} {_} {_} {_} {_} {_} {_} {_} _ {_} _.

(* How does comparing between first of params address work?
Let "a" and "b" are args
1. All neg num greater than pos ones;
2. If a and b is positive or negative both then they works usual
*)
Definition address_eqb {b1} (a: URValue address b1) {b2} (b: URValue address b2): URValue XBool (orb b1 b2).
assert (H2:(b1 || b2 || (b1 || b2)) = (b1 || b2)).
destruct b1 .
compute. auto.
compute. destruct b2 . auto. auto.
rewrite <- H2.

refine (uband (ueqb (addr_std_ι_address_right a) (addr_std_ι_address_right b)) 
        (ueqb (addr_std_ι_workchain_id_right a) (addr_std_ι_workchain_id_right b))).
Defined.

Definition address_uneqb {b1} (a: URValue address b1) {b2} (b: URValue address b2): URValue XBool (orb b1 b2).
refine (uneg (address_eqb a b)).
Defined.

Definition compare_wrapper' (compare_func: Z -> Z -> bool) (a:Z) (b:Z): bool :=
match (Z.ltb 0 a), (Z.ltb 0  b), (orb (Z.eqb a 0) (Z.eqb b 0)) with 
| _, _, true => compare_func a b
| true, true, _ => compare_func a b
| false, false, _ => compare_func a b
| true, false, _ => compare_func 2 1
| false, true, _ => compare_func 1 2
end.

Definition compare_wrapper  {b1} (a : URValue Z b1) {b2} (b : URValue Z b2)  (compare_func: Z -> Z -> bool) : URValue XBool (orb b1 b2).
pose proof (urvalue_bind a (fun a' => urvalue_bind b (fun b' => \\ # {compare_wrapper' compare_func a' b'} \\)): URValue _ _).
rewrite right_or_false in X.
refine X.
Defined.

(* 
    lexicographic order like
    (if "first1" = "first2" then (compare "second1" "second2") else (compare "first1" "first2")) := "(first1=first2)/\(compare second1 second2) \/ (first1!=first2)/\(compare first1 first2)"
*)

#[global] 
Program 
Instance binaryLogicalOperations_4 :  BinaryLogicalOperations address address XBool | 40 := {
    un_eqb   := fun (b1:bool) (x: URValue (address) b1) (b2:bool) (y: URValue (address) b2) => address_eqb x y; 
    un_uneqb := fun (b1:bool) (x: URValue (address) b1) (b2:bool) (y: URValue (address) b2) => address_uneqb x y;
    un_ltb   := fun (b1:bool) (x: URValue (address) b1) (b2:bool) (y: URValue (address) b2) => 
                let eq_first := un_eqb' (addr_std_ι_workchain_id_right x)(addr_std_ι_workchain_id_right y) in 
                ubor  (uband eq_first        (compare_wrapper (addr_std_ι_workchain_id_right x) (addr_std_ι_workchain_id_right y) Z.ltb)) 
                        (uband (uneg eq_first) (un_ltb' (addr_std_ι_address_right x) (addr_std_ι_address_right y)));
    un_leb   := fun (b1:bool) (x: URValue (address) b1) (b2:bool) (y: URValue (address) b2) => 
                let eq_first := un_eqb' (addr_std_ι_workchain_id_right x)(addr_std_ι_workchain_id_right y) in 
                ubor  (uband eq_first        (compare_wrapper (addr_std_ι_workchain_id_right x) (addr_std_ι_workchain_id_right y) Z.leb)) 
                        (uband (uneg eq_first) (un_leb' (addr_std_ι_address_right x) (addr_std_ι_address_right y)));
    un_gtb   := fun (b1:bool) (x: URValue (address) b1) (b2:bool) (y: URValue (address) b2) => 
                let eq_first := un_eqb' (addr_std_ι_workchain_id_right x)(addr_std_ι_workchain_id_right y) in 
                ubor  (uband eq_first        (compare_wrapper (addr_std_ι_workchain_id_right x) (addr_std_ι_workchain_id_right y) Z.gtb)) 
                        (uband (uneg eq_first) (un_gtb' (addr_std_ι_address_right x) (addr_std_ι_address_right y)));
    un_geb   := fun (b1:bool) (x: URValue (address) b1) (b2:bool) (y: URValue (address) b2) => 
                let eq_first := un_eqb' (addr_std_ι_workchain_id_right x)(addr_std_ι_workchain_id_right y) in 
                ubor  (uband eq_first        (compare_wrapper (addr_std_ι_workchain_id_right x) (addr_std_ι_workchain_id_right y) Z.geb)) 
                        (uband (uneg eq_first) (un_geb' (addr_std_ι_address_right x) (addr_std_ι_address_right y)));
}.
Next Obligation.
destruct b1;
destruct b2;
auto.
Defined.
Next Obligation.
destruct b1;
destruct b2;
auto.
Defined.
Next Obligation.
destruct b1;
destruct b2;
auto.
Defined.
Next Obligation.
destruct b1;
destruct b2;
auto.
Defined.
Fail Next Obligation.

Local Close Scope Z_scope.

End AddressEqb.

End tvmFuncDef.