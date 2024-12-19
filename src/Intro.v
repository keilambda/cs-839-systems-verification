(* terms, vernacular, tactics *)
(* Abort. *)

Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday monday).

Lemma next_weekday_test : next_weekday (next_weekday friday) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.

Definition next_day (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Lemma wednesday_has_prev_day : exists d, next_day d = wednesday.
Proof.
  exists tuesday.
  simpl. reflexivity.
Qed.

Lemma every_day_has_prev : forall d, exists d', next_day d' = d.
Proof.
  intros d.
  destruct d.
  - exists sunday. simpl. reflexivity.
  - exists monday. simpl. reflexivity.
  - exists tuesday. simpl. reflexivity.
  - exists wednesday. simpl. reflexivity.
  - exists thursday. simpl. reflexivity.
  - exists friday. simpl. reflexivity.
  - exists saturday. simpl. reflexivity.
Qed.

Module BooleanPlayground.

Inductive bool : Type :=
| true
| false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (a b : bool) : bool :=
  match a with
  | true => b
  | false => false
  end.

Definition orb (a b : bool) : bool :=
  match a with
  | true => true
  | false => b
  end.

Lemma test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Lemma test_orb2 : (orb false false) = false.
Proof. unfold orb. reflexivity. Qed.

Lemma test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Lemma test_orb4 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b : bool) : bool :=
  if b then false else true.

Definition andb' (a b : bool) : bool :=
  if a then b else false.

(* if works for any type with two constructors *)

Lemma andb'_eq_andb : forall a b, andb' a b = andb a b.
Proof.
  intros a b.
  destruct a, b; simpl; reflexivity.
Qed.

Fail Definition complex_expr1 (a b c : bool) :=
  orb (andb' b false) (andb (orb a b) c) b.

Definition complex_expr2 a b c :=
  andb (andb a (b (orb c a))) (b a).

End BooleanPlayground.

Module TuplePlayground.

Inductive bit : Type :=
| B1
| B0.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0) : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
| O
| S (n : nat).

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

End NatPlayground.

Module Option.

Inductive option (A : Type) :=
| Some (x : A)
| None.

Definition map {A B} (ma : option A) (f : A -> B) : option B :=
  match ma with
  | Some _ x => Some B (f x)
  | None _ => None B
  end.

Arguments Some {A} x.
Arguments None {A}.

Definition pure {A} (x : A) : option A := Some x.

Definition bind {A B} (ma : option A) (f : A -> option B) : option B :=
  match ma with
  | Some x => f x
  | None => None
  end.

Lemma pure_left_id {A B} (x : A) (f : A -> option B) : bind (pure x) f = f x.
Proof. reflexivity. Qed.

Lemma pure_right_id {A} (ma : option A) : bind ma pure = ma.
Proof. destruct ma; reflexivity. Qed.

Lemma bind_assoc {A B C} (ma : option A) (f : A -> option B) (g : B -> option C) :
  bind (bind ma f) g = bind ma (fun x => bind (f x) g).
Proof. destruct ma; reflexivity. Qed.

End Option.

Module MoreNatProofs.

(* Proof by computation *)
Lemma add_0_l n : 0 + n = n.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma O_or_succ n : n = 0 \/ n = S (Nat.pred n).
Proof.
  destruct n as [ | n'].
  -
    left.
    reflexivity.
  -
    right.
    simpl.
    reflexivity.
Qed.

Lemma eq_add_O_2 n m : n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros Hn Hm.
  rewrite Hn, Hm.
  simpl.
  reflexivity.
Qed.

(*
intros
rewrite
simpl
reflexivity
destruct (... as ...)
left
right
exists
unfold (... in ...)
discriminate
exfalso
exact ...
assumption
apply

Compute, Check, Locate, Print
 *)

Lemma neq_succ_0 n : S n <> 0.
Proof.
  Locate "<>".
  Locate "~".
  Print not.
  unfold not.
  intros Hn.
  discriminate.
Qed.

Lemma succ_pred n : n <> 0 -> n = S (Nat.pred n).
Proof.
  intros Hn.
  destruct (O_or_succ n) as [H0|HS].
  - unfold not in Hn.
    exfalso.
    apply Hn.
    exact H0.
  - assumption.
Qed.

End MoreNatProofs.
