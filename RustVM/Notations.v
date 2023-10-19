Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 

Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Rust.All.

Require Import Rust.Func.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope urust_scope.

Notation " 'RandomnessSource' '::' 'new' '()' " := 
    (wrapURValue (new_rs))
(in custom URValue at level 55) : urust_scope.

Notation " rs '->' 'next_u8' '()' " := (wrapURValue (nextu8_urvalue rs))
(in custom URValue at level 55, rs custom URValue) : urust_scope.

Notation " rs '->' 'next_u16' '()' " := (wrapURValue (nextu16_urvalue rs))
(in custom URValue at level 55, rs custom URValue) : urust_scope.

Notation " rs '->' 'next_u32' '()' " := (wrapURValue (nextu32_urvalue rs))
(in custom URValue at level 55, rs custom URValue) : urust_scope.

Notation " rs '->' 'next_u64' '()' " := (wrapURValue (nextu64_urvalue rs))
(in custom URValue at level 55, rs custom URValue) : urust_scope.

Notation " rs '->' 'next_u8_in_range' '(' mn ',' mx ')' " := (wrapURValue (nextu8_inrange rs mn mx))
(in custom URValue at level 55, rs custom URValue) : urust_scope.

Notation " rs '->' 'next_u16_in_range' '(' mn ',' mx ')' " := (wrapURValue (nextu16_inrange rs mn mx))
(in custom URValue at level 55, rs custom URValue) : urust_scope.

Notation " rs '->' 'next_u32_in_range' '(' mn ',' mx ')' " := (wrapURValue (nextu32_inrange rs mn mx))
(in custom URValue at level 55, rs custom URValue) : urust_scope.

Notation " rs '->' 'next_u64_in_range' '(' mn ',' mx ')' " := (wrapURValue (nextu64_inrange rs mn mx))
(in custom URValue at level 55, rs custom URValue) : urust_scope.




Notation " 'blockchain' '()' " := 
    (wrapURValue (new_bc))
(in custom URValue at level 55) : urust_scope.

Notation " bc '->' 'get_sc_address' '()' " := 
    (wrapURValue (get_sc_address' bc))
(in custom URValue at level 55, bc custom URValue) : urust_scope.

Notation " bc '->' 'get_owner_address' '()' " := 
    (wrapURValue (owner_address bc))
(in custom URValue at level 55, bc custom URValue) : urust_scope.

Notation " bc '->' 'get_caller' '()' " := 
    (wrapURValue (get_caller' bc))
(in custom URValue at level 55, bc custom URValue) : urust_scope.

Notation " bc '->' 'get_sc_balance' '(' token ',' nonce ')' " := 
    (wrapURValue (get_sc_balance' bc token nonce))
(in custom URValue at level 55, bc custom URValue) : urust_scope.

Notation " bc '->' 'get_block_timestamp' '()' " := 
    (wrapURValue (get_block_timestamp' bc))
(in custom URValue at level 55, bc custom URValue) : urust_scope.

Notation " bc '->' 'get_block_epoch' '()' " := 
    (wrapURValue (get_block_epoch' bc))
(in custom URValue at level 55, bc custom URValue) : urust_scope.

Notation " bc '->' 'get_block_round' '()' " := 
    (wrapURValue (get_block_round' bc))
(in custom URValue at level 55, bc custom URValue) : urust_scope.


Notation " 'call_value' '()' " :=
    ( wrapURValue (new_cv))  
(in custom URValue at level 55) : urust_scope.

Notation " cv '->' 'egld_value' '()' " := 
    ( wrapURValue (egld_value' cv))  
(in custom URValue at level 55, cv custom URValue) : urust_scope.

Notation " cv '->' 'all_esdt_transfers' '()' " := 
    ( wrapURValue (all_esdt_transfers' cv))  
(in custom URValue at level 55, cv custom URValue) : urust_scope.

(* TODO!!! multi_esdt<5>(), should work with any constant *)
Notation " cv '->' 'multi_esdt' '()' " := 
    ( wrapURValue (multi_esdt' (* TODO remove default *) default cv))  
(in custom URValue at level 55, cv custom URValue) : urust_scope.

Notation " cv '->' 'single_esdt' '()' " := 
    ( wrapURValue (single_esdt' cv))  
(in custom URValue at level 55, cv custom URValue) : urust_scope.

Notation " cv '->' 'single_fungible_esdt' '()' " := 
    ( wrapURValue (single_fungible_esdt' cv))  
(in custom URValue at level 55, cv custom URValue) : urust_scope.

Notation " cv '->' 'egld_or_single_esdt' '()' " := 
    ( wrapURValue (egld_or_single_esdt' cv))  
(in custom URValue at level 55, cv custom URValue) : urust_scope.

Notation " cv '->' 'egld_or_single_fungible_esdt' '()' " := 
    ( wrapURValue (egld_or_single_fungible_esdt' cv))  
(in custom URValue at level 55, cv custom URValue) : urust_scope.


Notation " tid '->' 'is_valid' '()' " := 
    ( wrapURValue (isvalid tid))  
(in custom URValue at level 55, tid custom URValue) : urust_scope.



Notation " 'send' '()' " :=
    ( wrapURValue (new_send))  
(in custom URValue at level 55) : urust_scope.

(* TODO: hack!!! *)
Notation " 'send' '()' " := 
    (wrapURValue (new_send))  
(in custom ULValue at level 55) : urust_scope.

Notation " snd '->' 'direct' '(' addr ',' tid ',' nonce ',' amount ')' " := 
    (direct_ulvalue snd addr tid nonce amount)
(in custom ULValue at level 55, snd custom ULValue,
                               addr custom URValue at level 55,
                               tid custom URValue at level 55,
                               nonce custom URValue at level 55,
                               amount custom URValue at level 55
                            ) : urust_scope.
