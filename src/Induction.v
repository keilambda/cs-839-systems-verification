Module NatDefs.

Inductive nat : Type :=
| O
| S (n : nat).

Fixpoint add (a b : nat) : nat :=
  match a with
  | O => b
  | S n => S (add n b)
  end.

End NatDefs.

Module MoreNatProofs.

Lemma add_0_l n : 0 + n = n.
Proof.
  simpl.
  reflexivity.
Qed.

(* Set Default Goal Selector "!". *)

Lemma add_0_r_failed n : n + 0 = n.
Proof.
  destruct n as [|n].
  - simpl. reflexivity.
  - simpl.
    destruct n as [|n].
Abort.

(*
induction ... (as ...)
*)

Lemma add_0_r n : n + 0 = n.
Proof.
  induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma or_intro_r (P Q : Prop) : Q -> P \/ Q.
Proof.
  intros HQ.
  right.
  assumption.
Qed.

Lemma or_elim (P Q R : Prop) : (P -> R) -> (Q -> R) -> (P \/ Q) -> R.
Proof.
  intros HPR HQR PQ.
  destruct PQ as [HP | HQ].
  - apply (HPR HP).
  - exact (HQR HQ).
Qed.

(* split, subst *)

Lemma and_intro (P Q : Prop) : P -> Q -> P /\ Q.
Proof.
  intros HP HQ.
  split.
  - assumption.
  - assumption.
Qed.

Lemma and_elim_r P Q : (P /\ Q) -> Q.
Proof.
  intros HPQ.
  destruct HPQ as [HP HQ].
  apply HQ.
Qed.

Lemma and_elim_l P Q : (P /\ Q) -> P.
Proof.
  intros HPQ.
  destruct HPQ as [HP HQ].
  assumption.
Qed.

Example and_or_example (P Q : Prop) : (P /\ Q) \/ (Q /\ P) -> P /\ Q.
Proof.
  intros H.
  destruct H as [HPQ | HQP].
  + assumption.
  + destruct HQP. split; assumption.
Qed.

Lemma and_O_iff n m : (n = 0 /\ m = 0) <-> n + m = 0.
Proof.
  Locate "<->".
  unfold iff.
  split.
  - intros [Hn Hm].
    subst.
    simpl.
    reflexivity.
  - intros H.
    destruct n as [|n].
    + rewrite add_0_l in H.
      split.
      { reflexivity. }
      assumption.
    + simpl in H.
      discriminate.
Qed.

Lemma add_succ_r a b : a + S b = S (a + b).
Proof.
  induction a as [|a IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma add_comm a b : a + b = b + a.
Proof.
  induction a as [|a IHn].
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite add_succ_r. rewrite IHn. reflexivity.
Qed.

End MoreNatProofs.

Module Option.

Definition some_ex : option nat := Some 3.

Definition none_ex : option nat := None.

Definition none_ex_2 := @None nat.
