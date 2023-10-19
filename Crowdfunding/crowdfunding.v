Require Import UrsusEnvironment.Rust.current.Environment.
Require Import UrsusContractCreator.BaseContracts.MultiversxContract.

Require Import Containers.

#[language=rust]
#[translation=off]
Contract CrowdFunding;  
Sends To;
Inherits
  MultiversxBaseContract
;
Types
  Inductive Status :=
    | st_FundingPeriod
    | st_Successful
    | st_Failed
;
Constants;
StorageMappers
  target (SingleValueMapper BigUint)
  deadline (SingleValueMapper u64)
  deposit (address -> SingleValueMapper BigUint)
  cf_token_identifier (SingleValueMapper EgldOrEsdtTokenIdentifier)
;
Record Contract := {
}.

SetUrsusOptions.
Unset Ursus Extraction.

Definition Status_eqb (s1 s2: Status) : bool :=
  match s1, s2 with
  | st_Failed, st_Failed => true
  | st_FundingPeriod, st_FundingPeriod => true
  | st_Successful, st_Successful => true
  | _, _ => false
  end.

Definition Status_eqb_right
  b1 (s1: URValue Status b1)
  b2 (s2: URValue Status b2)
  : URValue bool%urust (b1 || b2).
  epose proof (urvalue_bind (XBool:=bool) s1 (fun s1' => urvalue_bind s2 (fun s2' => URScalar (Status_eqb s1' s2')))).
  rewrite Bool.orb_false_r in X.
  exact X.
Defined.

Instance StatusBinOps :
  BinaryLogicalOperations LedgerLRecord ContractLRecord
    LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord Status
    Status bool.
constructor;
  exact Status_eqb_right.
Defined.

Instance XDefaultStatus : XDefault Status := {default := st_Failed}.

(*! TODO *)
Instance TokenBinOp : 
  BinaryLogicalOperations LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord
    MessagesAndEventsLRecord EgldOrEsdtTokenIdentifier EgldOrEsdtTokenIdentifier bool.
Admitted.

UseLocal Definition _ := [
    BigUint;
    PhantomType;
    Status;
    u64;
    EgldOrEsdtTokenIdentifier;
    EgldOrEsdtTokenPayment;
    u64;
    address;
    (SingleValueMapper BigUint)
  ].

(* fn get_current_time(&self) -> u64 { *)
(*     self.blockchain().get_block_timestamp() *)
(* } *)
Ursus Definition get_current_time : UExpression u64 false.
{
  ::// return_ blockchain()->get_block_timestamp() |.
}
return.
Defined.
Sync.

(* #[init] *)
(* fn init(&self, target: BigUint, deadline: u64, token_identifier: EgldOrEsdtTokenIdentifier) { *)
(*     require!(target > 0, "Target must be more than 0"); *)
(*     self.target().set(target); *)

(*     require!( *)
(*         deadline > self.get_current_time(), *)
(*         "Deadline can't be in the past" *)
(*     ); *)
(*     self.deadline().set(deadline); *)

(*     require!(token_identifier.is_valid(), "Invalid token provided"); *)
(*     self.cf_token_identifier().set(token_identifier); *)
(* } *)

Ursus Definition init
  (target': BigUint)
  (deadline': u64)
  (token_identifier': EgldOrEsdtTokenIdentifier)
  : UExpression PhantomType true.
{
  ::// require_ (target' > {0%N}, #{"Target must be more than 0"}).
  ::// target->svm_set(target').
  
  ::// require_ (deadline' > get_current_time(), #{"Deadline can't be in the past"}).
  ::// deadline->svm_set(deadline').

  ::// require_ (token_identifier'->is_valid(), #{"Invalid token provided"}).
  ::// cf_token_identifier->svm_set(token_identifier') |.
}
return.
Defined.
Sync.

(* fn get_current_funds(&self) -> BigUint { *)
(*     let token = self.cf_token_identifier().get(); *)

(*     self.blockchain().get_sc_balance(&token, 0) *)
(* } *)
Ursus Definition get_current_funds : UExpression BigUint true.
{
  ::// var token : _ := cf_token_identifier->svm_get() ; _ |.
  ::// return_ blockchain()->get_sc_balance(token, {0}) |.
}
return.
Defined.
Sync.

(* (* #[view] *) *)
(* (* fn status(&self) -> Status { *) *)
(* (*     if self.get_current_time() < self.deadline().get() { *) *)
(* (*         Status::FundingPeriod *) *)
(* (*     } else if self.get_current_funds() >= self.target().get() { *) *)
(* (*         Status::Successful *) *)
(* (*     } else { *) *)
(* (*         Status::Failed *) *)
(* (*     } *) *)
(* (* } *) *)
Ursus Definition status : UExpression Status true.
{
  ::// if (get_current_time() < deadline->svm_get()) then { ->/> }  else { ->/> } |.
  {
    ::// exit_ #{st_FundingPeriod} |.
  }
  {
    ::// if (get_current_funds() >= target->svm_get()) then { ->/> } else { ->/> } |.
    {
      ::// exit_ #{st_Successful} |.
    }
    {
      ::// exit_ #{st_Failed} |.
    }
  }
}
return.
Defined.
Sync.


(* #[endpoint] *)
(* #[payable("*")] *)
(* fn fund(&self) { *)
(*     let (token, _, payment) = self.call_value().egld_or_single_esdt().into_tuple(); *)

(*     require!( *)
(*         self.status() == Status::FundingPeriod, *)
(*         "cannot fund after deadline" *)
(*     ); *)
(*     require!(token == self.cf_token_identifier().get(), "wrong token"); *)

(*     let caller = self.blockchain().get_caller(); *)
(*     self.deposit(&caller).update(|deposit| *deposit += payment); *)
(* } *)

Ursus Definition fund : UExpression PhantomType true.
{
  ::// var
    ( token : EgldOrEsdtTokenIdentifier ,
      _unused : u64 ,
      payment : BigUint )
    := call_value()->egld_or_single_esdt() ; _ |.

  ::// var status' : Status := status() ; _ |.
  ::// require_ (status' == #{st_FundingPeriod},
                 #{"cannot fund after deadline"}
                ).
  ::// var token' : _ := cf_token_identifier->svm_get() ; _ |.
  ::// require_ (token == token', #{"wrong token"}).
  
  ::// var caller : _ := blockchain()->get_caller() ; _ |.
  ::// var d : _ := deposit [[caller]]; _ |.
  ::// d->svm_update( fun deposit' => // deposit' := deposit' + {payment} //) |.
}
return.
Defined.
Sync.

(* #[endpoint] *)
(* fn claim(&self) { *)
(*     match self.status() { *)
(*         Status::FundingPeriod => sc_panic!("cannot claim before deadline"), *)
(*         Status::Successful => { *)
(*             let caller = self.blockchain().get_caller(); *)
(*             require!( *)
(*                 caller == self.blockchain().get_owner_address(), *)
(*                 "only owner can claim successful funding" *)
(*             ); *)

(*             let token_identifier = self.cf_token_identifier().get(); *)
(*             let sc_balance = self.get_current_funds(); *)

(*             self.send() *)
(*                 .direct(&caller, &token_identifier, 0, &sc_balance); *)
(*         }, *)
(*         Status::Failed => { *)
(*             let caller = self.blockchain().get_caller(); *)
(*             let deposit = self.deposit(&caller).get(); *)

(*             if deposit > 0u32 { *)
(*                 let token_identifier = self.cf_token_identifier().get(); *)

(*                 self.deposit(&caller).clear(); *)
(*                 self.send().direct(&caller, &token_identifier, 0, &deposit); *)
(*             } *)
(*         }, *)
(*     } *)
(* } *)

Notation "'ebind' v 'as' k 'in' e" :=
(urvalue_expression v (fun k => e)) (in custom ULValue at level 50, v custom URValue, k binder).

Ursus Definition claim : UExpression PhantomType true.
{
  ::// ebind status() as k in ->/> |.
  :: (
      match k with
      | st_FundingPeriod =>
         // require_ ({false}, #{"cannot claim before deadline"}) //
      | st_Successful =>
        //
        var caller : address := blockchain()->get_caller() ;
        require_ (caller == blockchain()->get_owner_address(),
                  #{"only owner can claim successful funding"}) ;
        var token_identifier : _ := cf_token_identifier->svm_get() ;
        var sc_balance : _ := get_current_funds() ;
        send()->direct(caller, token_identifier, {0}, sc_balance)
        //
      | st_Failed =>
        //
        var caller : address := blockchain()->get_caller() ;
        var deposit1 : u256  := deposit[[caller]]->svm_get() ;
        if (deposit1 > {0}) then { 
          var token_identifier : _ := cf_token_identifier->svm_get() ;
          ( deposit[[caller]]->clear()  ;
          send()->direct(caller, token_identifier, {0}, deposit1)  )
        } //
     end
    ).
}
return.
Defined.
Sync.

EndContract.
GenerateLocalState 0 CrowdFunding.
GenerateLocalState CrowdFunding.
