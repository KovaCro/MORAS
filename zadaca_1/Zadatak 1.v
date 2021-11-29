Goal forall X Y, ~(X /\ Y) \/ (~X /\ Y) \/ (~X /\ ~Y) <-> ~(X /\ Y).
Proof.
split.
- intros. destruct H.
+ exact H.
+ destruct H.
++ unfold not. intros. apply H. destruct H0. exact H0.
++ destruct H. unfold not. intros. destruct H1. apply H. exact H1.
- intros. left. exact H.
Qed.

Goal forall X Y Z, ~(~X /\ Y /\ ~Z) /\ ~(X /\ Y /\ Z) /\ (X /\ ~Y /\ ~Z) <-> (X /\ ~Y /\ ~Z).
Proof.
split.
- intros. destruct H. destruct H0. exact H1.
- intros. split.
-- destruct H. destruct H0. unfold not. intros. destruct H2. apply H2. exact H.
-- destruct H. destruct H0. unfold not. split.
+ intros. destruct H2. destruct H3. apply H1. exact H4.
+ split.
++ exact H.
++ split.
+++ exact H0.
+++ exact H1.
Qed.