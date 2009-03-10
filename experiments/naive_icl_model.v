Require Import Setoid.

Axiom S : Type.
Axiom elt : S -> S -> Prop.
Axiom abs : (S -> Prop) -> S.

Coercion elt : S >-> Funclass.

Axiom beta : forall f x, abs f x <-> f x.

Definition russell := abs (fun s => ~s s).

Lemma russell_wtf : russell russell <-> ~russell russell.
  pose (e := beta (fun s:S => ~s s) russell).
  fold russell in e.
  simpl in e.
  assumption.
Qed.

Lemma contra : forall P:Prop, (P -> ~P) -> ~P.
 intuition.
Qed.

Goal False.
 pose russell_wtf.
 destruct i.
 pose (contra _ H).
 pose (H0 n).
 contradiction.
Qed.