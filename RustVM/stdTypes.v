Require Import UMLang.UrsusLib.
Require Import NArith.
Require Import FinProof.CommonInstances.
Require Import Solidity.stdTypes.
Declare Scope urust_scope. 
Delimit Scope urust_scope with urust.

Local Open Scope ursus_scope.
Local Open Scope urust_scope.
Import UrsusNotations.

(* TODO: change to N *)
Notation "'BigUint'" := (XUBInteger _256) (at level 9): urust_scope.
Notation "'BigInt'" := (XInteger) (at level 9): urust_scope.

Notation "'i8'" := (XInteger) (at level 9): urust_scope.
Notation "'i16'" := (XInteger) (at level 9): urust_scope.
Notation "'i32'" := (XInteger) (at level 9): urust_scope.
Notation "'isize'" := (XInteger) (at level 9): urust_scope.
Notation "'i64'" := (XInteger) (at level 9): urust_scope.

Notation "'u8'" := (XUBInteger _8) (at level 9): urust_scope.
Notation "'u16'" := (XUBInteger _16) (at level 9): urust_scope.
Notation "'u32'" := (XUBInteger _32) (at level 9): urust_scope.
Notation "'usize'" := (XUBInteger _32) (at level 9): urust_scope.
Notation "'u64'" := (XUBInteger _64) (at level 9): urust_scope.
Notation "'u128'" := (XUBInteger _128) (at level 9): urust_scope.
Notation "'u256'" := (XUBInteger _256) (at level 9): urust_scope.

Notation "'bool'" := (XBool) (at level 9): urust_scope.
Notation "'String'" := (XString) (at level 9): urust_scope.
Notation "'Option'" := (XMaybe) (at level 9): urust_scope.
Notation "'Vec'" := (listVector) (at level 9): urust_scope.
