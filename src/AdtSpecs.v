Require Import ssreflect.
From stdpp Require Import numbers fin_sets gmap.
Open Scope Z_scope.

Definition digit : Type := Z.
Definition big_int : Type := list digit.

Definition zero : big_int := [].
Definition from_digit (x : digit) : big_int := [x].

Definition digit_sum_carry (a b : digit) : (digit * digit) :=
  (a + b `mod` 10, a + b `div` 10).

Fixpoint add_one (b : big_int) (d : digit) : big_int :=
  match b with
  | [] => if bool_decide (d = 0) then [] else [d]
  | h :: t =>
    let (sum, carry) := digit_sum_carry h d in
    sum :: add_one t carry
  end.

Fixpoint add_with_carry (a b : big_int) (carry : digit) : big_int :=
  match a, b with
  | [], [] => if bool_decide (carry = 0) then [] else [carry]
  | da :: ta, [] => add_one (da :: ta) carry
  | [], db :: tb => add_one (db :: tb) carry
  | da :: ta, db :: tb =>
    let (sum, new_carry) := digit_sum_carry da db in
    add_one (sum :: add_with_carry ta tb new_carry) carry
  end.

Definition big_int_add (a b : big_int) : big_int :=
  add_with_carry a b 0.

Definition big_int_le (a b : big_int) : bool :=
  if bool_decide (Z.of_nat (length a) < Z.of_nat (length b)) then true
  else if bool_decide (Z.of_nat (length a) > Z.of_nat (length b)) then false
  else
    let fix cmp (x y : big_int) : bool :=
      match x, y with
      | [], [] => true
      | dx :: tx, dy :: ty =>
        if bool_decide (dx < dy) then true
        else if bool_decide (dx > dy) then false
        else cmp tx ty
      | _, _ => true
      end
    in cmp (rev a) (rev b).

(* Model-based specification; with interface; without definitions *)

Definition rep_type := Z.
Fixpoint big_int_rep (b : big_int) : rep_type :=
  match b with
  | [] => 0
  | d :: t => d + 10 * big_int_rep t
  end.

Lemma zero_spec : big_int_rep zero = 0.
Proof. reflexivity. Qed.

Lemma from_digit_spec x : 0 ≤ x < 10 → big_int_rep (from_digit x) = x.
Proof.
  intros. simpl.
  lia.
Qed.

Lemma bit_int_add_spec : forall a b, big_int_rep (big_int_add a b) = Z.add (big_int_rep a) (big_int_rep b).
Admitted.

Lemma big_int_le_spec : forall a b, big_int_le a b = bool_decide (big_int_rep a ≤ big_int_rep b).
Admitted.

Module deleteMap.

Notation V := nat.

Inductive map :=
  | mkMap (elements : gmap Z V) (deletions : gset Z).

Definition elements (m : map) : gmap Z V :=
  match m with
  | mkMap elements _ => elements
  end.

Definition deletions (m : map) : gset Z :=
  match m with
  | mkMap _ deletions => deletions
  end.

Definition empty_ : map := mkMap ∅ ∅.

Definition insert_ (k : Z) (v : V) (m : map) : map :=
  mkMap (insert k v (elements m)) (deletions m ∖ {[k]}).

Definition remove_ (k : Z) (m : map) : map :=
  mkMap (elements m) (deletions m ∪ {[k]}).

Definition lookup_ (k : Z) (m : map) : option V :=
  if bool_decide (k ∈ deletions m) then None
  else (elements m) !! k.

Definition rep (m : map) : gmap Z V :=
  filter (λ '(k, v), k ∉ deletions m) (elements m).

Lemma empty_spec : rep empty_ = ∅.
Proof.
  rewrite /rep /=.
  reflexivity.
Qed.

Lemma insert_spec k v m : rep (insert_ k v m) = insert k v (rep m).
Proof.
  rewrite /rep /=.
  apply map_eq. intros k'.
  destruct (decide (k' = k)).
  - subst. rewrite lookup_insert.
    apply map_lookup_filter_Some.
    rewrite lookup_insert.
    split.
    + auto.
    + set_solver.
  - rewrite lookup_insert_ne //.
    rewrite map_filter_insert_True.
    { set_solver. }
    rewrite lookup_insert_ne //.
    destruct (decide (k' ∈ deletions m)).
    {
      rewrite map_lookup_filter_None_2.
      { set_solver. }
      rewrite map_lookup_filter_None_2.
      { set_solver. }
      auto.
    }
    destruct (elements m !! k') as [v0|] eqn:Heqk'.
    + transitivity (Some v0).
      { apply map_lookup_filter_Some. split; auto. set_solver. }
      symmetry.
      apply map_lookup_filter_Some. set_solver.
    + rewrite -> map_lookup_filter_None_2 by set_solver.
      rewrite -> map_lookup_filter_None_2 by set_solver.
      auto.
Qed.

Lemma remove_spec k m : rep (remove_ k m) = delete k (rep m).
Proof.
  rewrite /rep /=.
  apply map_eq. intros k'.
  destruct (decide (k' = k)).
  - subst. rewrite lookup_delete.
    apply map_lookup_filter_None.
    set_solver.
  - rewrite lookup_delete_ne //.
    admit.
Admitted.

Lemma lookup_spec k m : lookup_ k m = (rep m) !! k.
Proof.
  rewrite /rep /=.
  rewrite /lookup_.
  destruct (bool_decide _).
  - rewrite map_lookup_filter_None_2 //.
    admit.
  - destruct (elements m !! k) eqn:H.
    + symmetry.
      apply map_lookup_filter_Some_2; auto.
      admit.
    + rewrite map_lookup_filter_None_2 //.
      set_solver.
Admitted.

End deleteMap.
(*  *)
