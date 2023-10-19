(* Require Import UrsusEnvironment.Solidity.current.Environment. *)
Require Import UrsusEnvironment.Rust.current.Environment.
(* Require Import UrsusEnvironment.Solidity.current.LocalGenerator. *)
(* Require Import UrsusContractCreator.BaseContracts.EverContract. *)





Section SingleValueMapper.

(* Variables Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  : Type. *)
Context {Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  : Type}.
Context `{ledgerClass: LedgerClass XBool Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  }.
Context {Lifr: listInfiniteFunRec_gen XList}.

Notation UExpression := (@UExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation ULValue := (@ULValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation URValue := (@URValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation wrapURExpression := (@wrapURExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _ _ ).
Notation wrapULExpression := (@wrapULExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _ _ _ ).
Notation ursus_call_with_args := (@ursus_call_with_argsL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _  ).

Context `{LocalStateField XHMap LedgerLocalState bool}.

Definition SingleValueMapper (T: Type) := option T.

Definition svm_is_empty {T} (svm: SingleValueMapper T) : bool :=
  match svm with None => true | _ => false end.

Definition usvm_is_empty {T} (svm: ULValue (SingleValueMapper T))
  : URValue bool false.
  epose proof (urvalue_bind svm (fun svm' => \\ #{svm_is_empty svm'} \\)).
  simpl in X.
  exact X.
Defined.


(* Definition svm_is_empty' {T} (svm: ULValue (SingleValueMapper T)) *)
(*   : UExpression bool false := *)
(*   // *)
(*     (* new 'b : bool @ "b" := svm->is_empty(); *) *)
(*     new 'b : bool @ "b" := (usvm_is_empty svm) ; *)
(*     return_ ^{b} *)
(* //. *)

Section SvmSet.

Definition svm_set {T} (svm: SingleValueMapper T) (t: T)  : SingleValueMapper T :=
  Some t.

Definition usvm_set {T} {b1} (svm: URValue (SingleValueMapper T) b1) {b2} (t: URValue T b2) : URValue (SingleValueMapper T) (orb b1 b2).
  epose proof (urvalue_bind svm (fun svm' => urvalue_bind t (fun t' => \\ #{svm_set svm' t'} \\)) : URValue _ _).
  rewrite Bool.orb_false_r in X.
  exact X.
Defined.

Definition svm_set' {T R} (svm: ULValue (SingleValueMapper T))
  {b} (t: URValue T b) : UExpression R b.
  epose proof (// svm := {usvm_set svm t} //).
  rewrite Bool.orb_false_l in X.
  exact X.
Defined.

Definition svm_set'' {T R} (svm: ULValue (SingleValueMapper T))
  (t: T) : UExpression R false.
  refine (svm_set' svm (URScalar t)).
Defined.

Definition svm_set_left {T R} (svm: ULValue (SingleValueMapper T))
  {b} (t: URValue T b)
  : UExpression R b
  := (wrapULExpression (ursus_call_with_args λ2LR svm_set'' svm t))
.

Definition svm_set_right {T} (svm: ULValue (SingleValueMapper T))
  {b} (t: URValue T b) : URValue (SingleValueMapper T) b :=
  wrapURExpression (ursus_call_with_args λ2LR svm_set'' svm t).

End SvmSet.

Section SvmGet.
Definition usvm_get {T} {b1} (svm: URValue (SingleValueMapper T) b1) : URValue T true.
  epose proof (urvalue_bind svm (fun svm' =>
                                   match svm' with
                                   | None => URResult ($ (ControlError 0))
                                   | Some x => URResult ($ (ControlValue true x))
                                   end
    )).
  rewrite Bool.orb_true_r in X.
  exact X.
Defined.
End SvmGet.

Section SvmClear.
Definition svm_clear {T} (svm: SingleValueMapper T) : SingleValueMapper T := None.

Definition usvm_clear {T} {b} (svm: URValue (SingleValueMapper T) b) : URValue (SingleValueMapper T) b.
  epose proof (urvalue_bind svm (fun svm' => \\ #{ svm_clear svm'} \\ )).
  rewrite Bool.orb_false_r in X.
  exact X.
Defined.

Definition svm_clear' {T} {R}
  (* {b} *)
  (* (svm: URValue (SingleValueMapper T) b) *)
  (svm: ULValue (SingleValueMapper T))
  : UExpression R false.
  epose proof (// svm := {usvm_clear svm} //).
  exact X.
Defined.
End SvmClear.

Section SvmUpdate.
  Definition svm_update {T}
    (svm: SingleValueMapper T)
    (f: T -> T)
    : SingleValueMapper T :=
    match svm with
    | None => None
    | Some x => Some (f x)
    end.

  Definition svm_update_left {T R}
    `{XDefault T}
    `{LocalStateField XHMap LedgerLocalState T}
    (svm: ULValue (SingleValueMapper T))
    (f: ULValue T -> UExpression R false)
    : UExpression R true.
    refine //
      new 'x : T @ "x" := {usvm_get \\ svm \\} ; {f x}
    //.
  Defined.

  Definition svm_update_right {T R}
    `{XDefault T}
    `{XDefault R}
    `{LocalStateField XHMap LedgerLocalState T}
    (svm: ULValue (SingleValueMapper T))
    (f: ULValue T -> UExpression R false)
    : URValue R true.
    epose proof (svm_update_left svm f).
    refine (wrapURExpression (ursus_call_with_args λ0 X)).
  Defined.
  
End SvmUpdate.


End SingleValueMapper.

Notation " m '->' 'svm_set' '(' kv ')' " := (svm_set_left m kv)
    (in custom ULValue at level 55 , m custom ULValue, kv custom URValue) : urust_scope.     
Notation "m '->' 'svm_get(' ')'" := (wrapURValue (usvm_get m))
    (in custom URValue at level 55, m custom URValue) : urust_scope.
Notation "m '->is_empty()'" := (wrapURValue (usvm_is_empty m))
    (in custom URValue at level 55, m custom URValue) : urust_scope.
Notation "m '->svm_clear()'" := (svm_clear' m)
    (in custom ULValue at level 55, m custom ULValue) : urust_scope.
Notation "m '->svm_update(' f ')'" :=
  (svm_update_right m f)
    (in custom URValue at level 55,
        m custom URValue
        , f constr
    ) : urust_scope.
Notation "m '->svm_update(' f ')'" :=
  (svm_update_left m f)
    (in custom ULValue at level 55,
        m custom ULValue
        ,f constr
    ) : urust_scope.

(* Check \\ {_}->svm_update1( _ ) \\. *)
(* Check // {_}->svm_update2( fun x => // x := x // ) //. *)

Section VecMapper.

(* Variables Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  : Type. *)
Context {Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  : Type}.
Context `{ledgerClass: LedgerClass XBool Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  }.
Context {Lifr: listInfiniteFunRec_gen XList}.

Notation UExpression := (@UExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation ULValue := (@ULValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation URValue := (@URValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation wrapURExpression := (@wrapURExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _ _ ).
Notation wrapULExpression := (@wrapULExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _ _ _ ).
Notation ursus_call_with_args := (@ursus_call_with_argsL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _  ).

Context `{LocalStateField XHMap LedgerLocalState bool}.

Definition VecMapper (T: Type) := listVector T.

Section VecIsEmpty.
  Definition vec_is_empty {T} (v: VecMapper T) : bool :=
    match v with wrap _ l =>
    match l with
    | Datatypes.nil => true
    | _ => false
    end end.
  Definition uvec_is_empty {T} {b} (v: URValue (VecMapper T) b) : URValue bool b.
    epose proof (urvalue_bind v (fun v' => \\ #{ vec_is_empty v' } \\)).
    rewrite Bool.orb_false_r in X.
    refine X.
  Defined.
End VecIsEmpty.

Section VecClear.
  Definition vec_clear {T} (v: VecMapper T) : VecMapper T := wrap _ Datatypes.nil.
  Definition uvec_clear {T} {b}
    (v: URValue (VecMapper T) b)
    : URValue (VecMapper T) b.
    epose proof (urvalue_bind v (fun v' => \\ #{ vec_clear v' } \\)).
    rewrite Bool.orb_false_r in X.
    exact X.
  Defined.

  Definition vec_clear' {T R}
    (* {b} *)
    (v: ULValue (VecMapper T))
    : UExpression R false.
    epose proof (// v := {uvec_clear v} //).
    exact X.
  Defined.
End VecClear.

End VecMapper.

Notation "m '->vec_is_empty()'" := (wrapURValue (uvec_is_empty m))
    (in custom URValue at level 55, m custom URValue) : urust_scope.

Notation "m '->' 'vec_clear()'" := (vec_clear' m)
    (in custom ULValue at level 55, m custom ULValue) : urust_scope.

Section UnorderedSetMapper.

(* Variables Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  : Type. *)
Context {Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  : Type}.
Context `{ledgerClass: LedgerClass XBool Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  }.
Context {Lifr: listInfiniteFunRec_gen XList}.

Notation UExpression := (@UExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation ULValue := (@ULValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation URValue := (@URValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation wrapURExpression := (@wrapURExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _ _ ).
Notation wrapULExpression := (@wrapULExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _ _ _ ).
Notation ursus_call_with_args := (@ursus_call_with_argsL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _  ).

Context `{LocalStateField XHMap LedgerLocalState bool}.
Definition UnorderedSetMapper (T: Type) := listVector T.

Section UsmClear.
  Definition usm_clear {T} (usm: UnorderedSetMapper T) : UnorderedSetMapper T := wrap _ (Datatypes.nil).
  Definition uusm_clear {T} {b} (usm: URValue (UnorderedSetMapper T) b) : URValue (UnorderedSetMapper T) b.
  epose proof (urvalue_bind usm (fun usm' => \\ #{ usm_clear usm'} \\ )).
  rewrite Bool.orb_false_r in X.
  exact X.
Defined.

Definition usm_clear' {T} {R}
  (usm: ULValue (UnorderedSetMapper T))
  : UExpression R false.
  epose proof (// usm := {uusm_clear usm} //).
  exact X.
Defined.
  
End UsmClear.

End UnorderedSetMapper.

Notation "m '->' 'usm_clear()'" := (usm_clear' m)
    (in custom ULValue at level 55, m custom ULValue) : urust_scope.

Section Classes.

Variables Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  : Type.
Context `{ledgerClass: LedgerClass XBool Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents  }.
Context {Lifr: listInfiniteFunRec_gen XList}.

Notation UExpression := (@UExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation ULValue := (@ULValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation URValue := (@URValueL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass) .
Notation wrapURExpression := (@wrapURExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _ _ ).
Notation wrapULExpression := (@wrapULExpressionL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _ _ _ ).
Notation ursus_call_with_args := (@ursus_call_with_argsL Ledger LedgerMainState LedgerLocalState LedgerVMState LedgerMessagesAndEvents   ledgerClass _ _  ).

(* About ULtoRValue. *)
(* Search "URto". *)

Class HasClear (C: Type) := {
    clear_func :
    forall {R: Type},
      ULValue C ->
      UExpression R false
  }.

(* Definition svm_clear' {T} {R} *)
(*   (* {b} *) *)
(*   (* (svm: URValue (SingleValueMapper T) b) *) *)
(*   (svm: ULValue (SingleValueMapper T)) *)
(*   : UExpression R false. *)
(* Definition usm_clear' {T} {R} *)
(*   (usm: ULValue (UnorderedSetMapper T)) *)
(*   : UExpression R false. *)
#[export]
Instance HasClearSvm : forall T, HasClear (SingleValueMapper T).
constructor.
epose proof (@svm_clear' _ _ _ _ _ _ T).
exact X.
Defined.

#[export]
Instance HasClearVec : forall T, HasClear (VecMapper T).
constructor.
epose proof (@vec_clear' _ _ _ _ _ _ T).
exact X.
Defined.

#[export]
Instance HasClearUsm : forall T, HasClear (UnorderedSetMapper T).
constructor.
epose proof (@usm_clear' _ _ _ _ _ _ T).
exact X.
Defined.

End Classes.

Notation "m '->clear()'" := (clear_func _ _ _ _ _ m)
                             (in custom ULValue at level 55,
                             m custom ULValue) : urust_scope.

Notation BidUint := (XUBInteger 256).