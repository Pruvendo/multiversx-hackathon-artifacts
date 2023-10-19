Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 

Require Import FinProof.Common. 
Require Import FinProof.CommonInstances. 
Require Import FinProof.EpsilonMonad.
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.MonadTransformers21. 
Require Import FinProof.Types.IsoTypes. 

Require Import FinProof.Lib.BoolEq. 

Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusStdLib.Rust.All.

(* Require Import Func. *)

(* Inductive InternalMessageParamsFields :=
| InternalMessage_ι_dest (* address *)
| InternalMessage_ι_sender (* address *)
| InternalMessage_ι_value (* uint128 *)
| InternalMessage_ι_bounce (* bool *)
| InternalMessage_ι_flag (* uint16 *)
| InternalMessage_ι_body (* TvmCell *)
| InternalMessage_ι_stateInit (* TvmCell *)
| InternalMessage_ι_answerId (* uint32 *)
| InternalMessage_ι_createdAt. (* uint32 *) *)

(* Inductive ExternalMessageParamsFields := 
| ExternalMessage_ι_dest (* address *)
| ExternalMessage_ι_time (* uint64 *)
| ExternalMessage_ι_expire (* uint32 *)
| ExternalMessage_ι_body (* TvmCell *)
| ExternalMessage_ι_pubkey (* uint256 *)
| ExternalMessage_ι_callbackId (* uint32 *)
| ExternalMessage_ι_onErrorId (* uint32 *)
| ExternalMessage_ι_stateInit (* TvmCell *)
| ExternalMessage_ι_signBox (* TvmCell *)
| ExternalMessage_ι_flags. (* uint8 *) *)


Local Open Scope struct_scope.
Local Open Scope urust_scope.

Definition TokenIdentifier := string.
Definition EgldOrEsdtTokenIdentifier := option TokenIdentifier.

Inductive EsdtTokenPaymentFields :=
| EsdtTokenPayment_ι_identifier
| EsdtTokenPayment_ι_nonce
| EsdtTokenPayment_ι_amount.
Definition EsdtTokenPaymentL := [TokenIdentifier : Type ; u64 : Type ; BigUint : Type ]%llist.
LocalGeneratePruvendoRecord EsdtTokenPaymentL EsdtTokenPaymentFields.
Definition EsdtTokenPayment := EsdtTokenPaymentLRecord.

Inductive EgldOrEsdtTokenPaymentFields :=
| EgldOrEsdtTokenPayment_ι_identifier
| EgldOrEsdtTokenPayment_ι_nonce
| EgldOrEsdtTokenPayment_ι_amount.
Definition EgldOrEsdtTokenPaymentL := [EgldOrEsdtTokenIdentifier : Type ; u64 : Type ; BigUint : Type ]%llist.
LocalGeneratePruvendoRecord EgldOrEsdtTokenPaymentL EgldOrEsdtTokenPaymentFields.
Definition EgldOrEsdtTokenPayment := EgldOrEsdtTokenPaymentLRecord.

Inductive GeneralMessageParamsFields :=
(*| GeneralMessage_ι_isExternal (* bool *)*)
| GeneralMessage_ι_dest (* address *)
(*| GeneralMessage_ι_time (* uint64 *)*)
(*| GeneralMessage_ι_flags (* uint16 *)
| GeneralMessage_ι_callbackId (* uint32 *)*)

(*| ExternalMessage_ι_expire (* uint32 *)
| ExternalMessage_ι_onErrorId (* uint32 *)*)

| InternalMessage_ι_sender (* address *)
| InternalMessage_ι_value (* BigUint *)
| InternalMessage_ι_tokens (* XList EsdtTokenPayment *)
(*| InternalMessage_ι_bounce (* bool *)*).

Inductive PersistentContractDataFields :=
| PersistentContractData_ι_owner (* address *)
| PersistentContractData_ι_balance (* uint128 *)
| PersistentContractData_ι_tokens (* XHMap (TokenIdentifier * u64) BigUint *)
| PersistentContractData_ι_address (* address *).

Inductive addr_stdFields := | add_std_ι_workchain_id | add_std_ι_address.

(* Import UrsusNotations.*)

Global Notation TVMEvent := (PhantomType) (only parsing).

Definition addr_stdL := [XInteger : Type ; u256 : Type ]%llist.
LocalGeneratePruvendoRecord addr_stdL addr_stdFields.
Definition address := addr_stdLRecord.


(* Definition OutgoingMessageParamsL := [address : Type ; uint128 : Type; uint16: Type ]%llist.
LocalGeneratePruvendoRecord OutgoingMessageParamsL OutgoingMessageParamsFields. *)

Import UrsusNotations.
Local Open Scope ursus_scope.

(* Definition InternalMessageParamsL := [ address: Type; address: Type; uint128 : Type ; XBool : Type ; uint16 : Type; TvmCell : Type; TvmCell : Type; uint32: Type; uint32: Type ]%llist.
LocalGeneratePruvendoRecord InternalMessageParamsL InternalMessageParamsFields.

Definition ExternalMessageParamsL := [ address: Type; uint64 : Type ; uint32 : Type ; TvmCell : Type; uint256 : Type; uint32 : Type; uint32: Type; TvmCell: Type ; TvmCell: Type; uint8: Type]%llist.
LocalGeneratePruvendoRecord ExternalMessageParamsL ExternalMessageParamsFields.
 *)

(* Inductive GeneralMessageParamsFields :=
| GeneralMessage_ι_dest (* address *)

| InternalMessage_ι_sender (* address *)
| InternalMessage_ι_value (* BigUint *)
| InternalMessage_ι_tokens (* list EsdtTokenPayment *)
*)

Definition GeneralMessageParamsL := [ address: Type; address: Type; BigUint: Type; XList EsdtTokenPayment: Type ]%llist.
LocalGeneratePruvendoRecord GeneralMessageParamsL GeneralMessageParamsFields.


Notation MultivMessage := (GeneralMessageParamsLRecord).

(* | ExternalEverMessage : ExternalMessageParamsLRecord -> EverMessage
| InternalEverMessage : InternalMessageParamsLRecord -> EverMessage. *)

(* Inductive PersistentContractDataFields :=
| PersistentContractData_ι_owner (* address *)
| PersistentContractData_ι_balance (* BigUint *)
| PersistentContractData_ι_tokens (* XHMap (TokenIdentifier * u64) BigUint *)
| PersistentContractData_ι_address (* address *)*)
Definition PersistentContractDataL := [address: Type; BigUint: Type; XHMap (TokenIdentifier * u64) BigUint; address: Type]%llist.
LocalGeneratePruvendoRecord PersistentContractDataL PersistentContractDataFields.

Section Messages.

Variables PublicInterface: Type.

Inductive OutgoingMessage :=
  | EmptyMessage : MultivMessage -> OutgoingMessage
  | OutgoingInternalMessage : MultivMessage -> PublicInterface -> OutgoingMessage.

End Messages.

#[global] 
Instance GeneralMessageParamsLRecord_default: XDefault GeneralMessageParamsLRecord | 0 :=
{ default :=  default }.

Lemma GeneralMessageParamsL_diff: forall (f1 f2: GeneralMessageParamsFields) (v2: field_type f2) 
                                         (r : GeneralMessageParamsLRecord ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
intros.
  destruct f1; destruct f2;
  (revert r;
	apply (countable_prop_proof (T:= GeneralMessageParamsLRecord ));
	cbv;
	first [reflexivity| contradiction]).
Qed.

Lemma add_stdL_diff: forall (f1 f2: addr_stdFields) (v2: field_type f2) (r : addr_stdLRecord ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
intros.
  destruct f1; destruct f2;
  (revert r;
	apply (countable_prop_proof (T:= address ));
	cbv;
	first [reflexivity| contradiction]).
Qed.

(* Lemma OutgoingMessageParamsL_diff: forall (f1 f2: OutgoingMessageParamsFields) (v2: field_type f2) (r : OutgoingMessageParamsLRecord ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
intros.
  destruct f1; destruct f2;
  (revert r;
	apply (countable_prop_proof (T:= OutgoingMessageParamsLRecord ));
	cbv;
	first [reflexivity| contradiction]).
Qed. *)

Lemma PersistentContractDataL_diff: forall (f1 f2: PersistentContractDataFields) (v2: field_type f2) (r : PersistentContractDataLRecord ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
intros.
  destruct f1; destruct f2;
  (revert r;
	apply (countable_prop_proof (T:= PersistentContractDataLRecord ));
	cbv;
	first [reflexivity| contradiction]).
Qed.

Arguments OutgoingInternalMessage {_}.

#[global] 
Instance OutgoingMessage_default : forall I, XDefault (OutgoingMessage I) :=
{
    default := EmptyMessage I default
}.

(* Check default: EverMessage. *)

(* #[global] 
Instance EverMessage_default:  XDefault (EverMessage) :=
{
    default := InternalEverMessage default
}. *)

Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Inductive VMStateFields := 
(* | VMState_ι_msg_pubkey (* message -> messagesAndEvents *) *)
(* | VMState_ι_now *) (* here *)
(* | VMState_ι_timestamp (* message -> messagesAndEvents/? *) *)
| VMState_ι_block_timestamp (* u64 *)
| VMState_ι_block_epoch (* u64 *)
| VMState_ι_block_round (* u64 *)
(* | VMState_ι_msg_sender (* message -> messagesAndEvents *) *)
(* | VMState_ι_msg_value (* message -> messagesAndEvents *) *)
(* | VMState_ι_msg_data (* message -> messagesAndEvents *) *)
(*| VMState_ι_accepted (* here *)
| VMState_ι_reserved (* here *) *)
| VMState_ι_isCommitted (* here *)
(**| VMState_ι_isTVMExited (* here *)*)
| VMState_ι_tracingList (* here *)
(*| VMState_ι_replayProtTime (* ? *)*)
| VMState_ι_random 
| VMState_ι_currentInboudMessage (* MultivMessage *).

Inductive IDefault := | _transfer :  IDefault.

Definition VMStateL := [u64 : Type ; u64 : Type ; u64 : Type ; XBool:Type; List.list TracingTree; u32 : Type; MultivMessage: Type]%glist.
GlobalGeneratePruvendoRecord VMStateL VMStateFields.

(* #[local]
Notation ULValue := (@ULValueL Ledger LedgerMainState LedgerLocalState VMStateLRecord LedgerMessagesAndEvents VMLedgerClass) .

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
}. *)

Lemma VMStateL_diff : forall (f1 f2: VMStateFields) (v2: field_type f2) (r : VMStateLRecord ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
intros.
  destruct f1; destruct f2;
  (revert r;
	apply (countable_prop_proof (T:= VMStateLRecord ));
	cbv;
	first [reflexivity| contradiction]).
Qed.


Definition XCommittedEmbedded: EmbeddedType VMStateLRecord XBool := VMStateLEmbeddedType VMState_ι_isCommitted.
Definition XTracingListEmbedded: EmbeddedType VMStateLRecord (List.list TracingTree) := VMStateLEmbeddedType VMState_ι_tracingList.
