From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun Lia.
Require Import sets.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope set_scope.
Delimit Scope set_scope with set.
Local Open Scope set_scope.

(******************************)
(* The real demo begins here. *)
(******************************)

Definition even : set nat := [set n | exists m, n = 2 * m].

(* n \in even is how we write that n is even, using standard set theory      *)
(*  notation.                                                                *)
Check fun n : nat => n \in even.

(* However, even, can also be used as a type, thanks to a coercion.          *)
(* And thanks to a second coercion, any even number can be used where        *)
(* a member of the supertype (here nat) is expected.                         *)
Check fun n : even => n * 3.

(* When n is natural number, the formula saying that if x is even, its       *)
(* triple also is, this formula is well-formed.                              *)
Check fun x => x \in even -> x * 3 \in even.

(* However, with the current stored knowledge, there is no way for the       *)
(* system to guess that, if n is even, its triple also is.                   *)
Fail Check fun n : even => (n * 3 : even).

Notation "x" := (MemType.sort x) (at level 0, only printing).

(* Still, we can prove that the triple of an even number is even.            *)
Lemma times_3_even (n : even) : n * 3 \in even.
Proof.
move: (memP n).
rewrite !setE.
move=> -[m ->].
exists (m * 3).
lia.
Qed.

HB.instance Definition _ (x : even) := times_3_even x.

Check (fun x : even => ((x * 3) * 3 : even)).

(* Now addressing a more complex extension. *)
HB.mixin Record hasAdd T := { add : T -> T -> T }.

(* addType is an alias for Add.type *)
#[short(type="addType")]
HB.structure Definition Add := {T of hasAdd T}.

Notation "x" := (Add.sort x) (at level 1, only printing).
Notation "x" := (@Add.Pack x _) (at level 1, only printing).

Notation "x +_ T y" := (@add T (x : T) (y : T) : T)
   (T at level 0, at level 60, format "x  +_ T  y", only parsing).
Notation "a + b" := (@add _ a b).

(* In what follows we call "additive set" a member of addSet *)
Definition addSet (T : addType) :=
  [set X : set T | forall a b, a \in X -> b \in X -> (a +_T b) \in X].

(* P : set T, is automatically usable as the type containing the elements
  of T who are in P.  On top of this, by the previous definition, adding two
  such elements gives an element of T that is still in P. Type theory does not
  make it possible to write x + y : P as the conclusion of the lemma. *)
Lemma mem_add (T : addType) (P : addSet T)
   (x : P) (y : P) : x +_T y \in P.
Proof.
move: (memP P).
(* in the resulting goal, P is used: 1/ as a type in the context,
   as a set in the conclusion. *)
rewrite setE.
(* Fail Timeout 1 apply. *)
by move=> /(_ x y); apply; apply/memP.
(* by []. *)
Qed.

(* We make sure that mem_add will be used to solve type class for membership
  of an addition in an additive set. *)
HB.instance Definition _ T P x y := @mem_add T P x y.

(* @hasAdd.Build .... has type hasAdd.axioms_ , but Hierarchy build completes
  the construction and makes this a tool build instances of type addType *)
(* TODO: Why do I need to pack by hand here?
  Also, the head of `P` is `MemType.sort` which is not characteristic **at all** of what we are doing. *)
HB.instance Definition _ (T : addType) (P : addSet T) := 
  @hasAdd.Build P (fun x y : P => MemType.pack_ (mem_add x y)).
(* This is just an example of usage, not used extensively later. *)
Example add_in_subset_equiv_superset (T : addType) (P : addSet T) (x y : P) :
  x +_P y = x +_T y :> T.
Proof. by []. Qed.

(* We define an addition on the type of subsets. *)
Definition add_set (T : addType) (X Y : set T) : set T :=
  MkSet (fun z => exists (x : X) (y : Y), z = x +_T y).

(* Thanks to this instance definition, whenever we wish to talk about an
  addition on sets, we know the operation is add_set. *)
HB.instance Definition _ (T : addType) : hasAdd (set T) :=
   hasAdd.Build (set T) (@add_set T).

(* We wish to prove that the sum of two additive sets is also additive, but this
  is only guaranteed if the addition operation is associative and commutative,
  which was not mentioned (in spite of the choice of name for the operation) *)
HB.mixin Record add_is_AC T of Add T := {
  addA_subproof : associative (@add T);
  addC_subproof : commutative (@add T)
}.

#[short(type="acAddType")]
HB.structure Definition AcAdd := {T of Add T & add_is_AC T}.

Notation "x" := (AcAdd.sort x) (at level 1, only printing).
Notation "x" := (@AcAdd.Pack x _) (at level 1, only printing).

(* These lemma will be used in subadd_add *)
Lemma addA (T : acAddType) : associative (@add T).
Proof. by case: T => T [] Tadd []. Qed.

Lemma addC (T : acAddType) : commutative (@add T).
Proof. by case: T => T [] Tadd []. Qed.

Lemma addAC (T : acAddType) : interchange (@add T) (@add T).
Proof.
move=> x y z t; rewrite !addA.
congr (_ +_T _).
rewrite -!addA.
congr (_ + _).
exact: addC.
Qed.

(* addSet T is a part of set T, it contains all the additive subsets. *)
(* We wish to prove that it is additive, as a part of setT, where the *)
(* addition operation is add_set *)
(*Lemma subadd_add (T : acAddType) : addSet T \in addSet (set T).
Proof.
(* this expands the definition of being an additive set at the level 
  elements sets. *)
rewrite setE. 
move=> P Q Padd Qadd.
(* this expands the definition of being an additive set at the level 
  elements of T. *)
rewrite setE. 
move=> a b.
(* this expands the definition of the addition of two sets. *)
rewrite 3!setE.
move=> [a1 [a2 <-]] [b1 [b2 <-]].
exists (a1 + b1), (a2 + b2).
rewrite addAC.
(* a1 + b1 is packed value whose first projection is an addition, the
f
ollowing rewrite exhibits the result of that addition. *)
rewrite /=.
by [].
Qed.

#[verbose]
   HB.instance Definition _ T := @subadd_add T.*)



(* I. Type structures *)
(* We declare nat to be an addType *)
HB.instance Definition _ := hasAdd.Build nat plus.
Lemma nat_add_is_AC : add_is_AC.axioms_ nat (Add.class (nat : addType)).
Proof.
split; [exact: PeanoNat.Nat.add_assoc | exact: PeanoNat.Nat.add_comm].
Qed.

HB.instance Definition _ := nat_add_is_AC.

(* Thanks to these declarations and the setup, all of these are addTypes *)
(* The sets of a type with addition can be provided with an addition as well *)
(* (see set_add above) *)
(* This is an an example of stability at typelevel *)
(* Inference is automatic *)
Check nat                 : addType.
Check set nat             : addType.
Check set (set nat)       : addType.
Check set (set (set nat)) : addType.

(* II. Set structure *)

Lemma even_subAdd : even \in (addSet nat).
Proof.
rewrite setE. 
move=> /= a b.
rewrite 3!setE.
move=> [m/= ->].
move=> [n/= ->].
by exists (m + n); rewrite /add/=; lia.
Qed.

HB.instance Definition _ := even_subAdd.

Lemma even0 : 0 \in even.
Proof.
rewrite setE.
exists 0.
by [].
Qed.

(* ref: 0_is_even *)
HB.instance Definition _ := even0.

(*
  This is an example of set stability property:
  additively stable subsets of a type with associative-commutative addition
  are preserved by set level addition.
  (see subadd_add above)
*)

Goal (even + even) \in addSet nat. Proof. by []. Qed.

(* This says almost the same thing, but addSet nat is used as a type here. *)
Check even + even : addSet nat.
(* In the next line, the addition forces the system to forget that even
   is already an addSet nat, but inference recovers this information. *)
Check even +_(set nat) even : addSet nat.
(* and this can be repeated. *)
Check even +_(set nat) even +_(set nat) even : addSet nat.
Check even +_(set nat) even +_(set nat) even +_(set nat) even : addSet nat.

(* III. Elements *)
(* Their stability is deduced from the structures of the sets *)
(* Here stability by + and 0 from the structure of the sets is *)
(* reused for automated inference of membership *)
(*
Note there is barely a difference between
 - (n : nat) (_ : n \is even)
 - and (n : even)
*)
Section tests.
Variables (Peven : even -> Prop) (Pnateven : forall n, n \in even -> Prop).
Variables (n : nat) (n_even : n \in even) (m : even) (p : nat).

Check Peven m : Prop. (* trivial *)
Check @Pnateven m _ : Prop. (* coercion from even to nat,
                               the proof part is automatic *)
Check Peven n : Prop. (* reconstruction of even from nat *)
Check @Pnateven n _ : Prop. (* proof found automatically *)

(* all the following are possible and the first two equivalent *)
Check n + m : nat.
Check n +_nat m.
(* Inference is done on the first term, but in this case it does not change
  the apparent behavior, because the notation casts to nat. *)
Check m +_nat n.
Check m +_nat p.
(* the order enforces th addition to be in even, but p is not a priori even. *)
Fail Check m + p.
(* Here the addition is in nat, so no worry with m. *)
Check p + m.

(* all the following are possible and the first two equivalent *)
Check m + n.
Check m +_even n.
Check n +_even m.
Check n + m : even.

Check (n : even) + m.
Check (m : nat) + n.
Check (m : nat) + n : nat.

End tests.

Example add_even (m n : even) : m +_nat n \in even.
(* automatic inference of even by stability by addition *)
Proof. by []. Qed.

Variable any_set : set nat.

Example any_set2P (m n : any_set) : m +_nat n  \in any_set + any_set.
Proof. by []. Qed.

(* even + even automatically preserves addition of natural numbers too *)
Lemma add_even2 (m n : even +_(set nat) even) : m +_nat n \in even + even.
Proof. by []. Qed.

Lemma evenDeven_eq_even : even + even = even.
Proof.
apply/eq_setP.
move=> n.
split.
  rewrite setE => -[] x [] y.
  by move=> <-.
move=> n_even.
rewrite setE.

(* This succeeds because of the instance definition at ref:0_is_even *)
exists 0.

(* The proof ends with 

  - by exists (MemType.Pack n_even)=> /=.

  but we would like to avoid the burden of knowing MemType.Pack to the
  user. 

  The following also works:

  - by rewrite /=; exists n.

  n_even is the crucial bit of information here, but finding it automatically
  is problematic, because blind search raises unification problems that loop.
*)
Fail Timeout 1 exists n.
rewrite /=.
exists n.
by [].
Qed.

