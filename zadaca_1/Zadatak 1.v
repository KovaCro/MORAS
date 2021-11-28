Goal forall X Y, ~(X /\ Y) \/ (~X /\ Y) \/ (~X /\ ~Y) -> ~(X /\ Y).
Proof.
intros. destruct H.
- exact H.
- destruct H.
+ unfold not. intros. apply H. destruct H0. exact H0.
+ destruct H. unfold not. intros. destruct H1. apply H. exact H1.
Qed.

Goal forall X Y Z, ~(~X /\ Y /\ ~Z) /\ ~(X /\ Y /\ Z) /\ (X /\ ~Y /\ ~Z) -> (X /\ ~Y /\ ~Z).
Proof.
intros. destruct H. destruct H0. exact H1.
Qed.