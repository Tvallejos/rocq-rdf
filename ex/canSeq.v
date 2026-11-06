From mathcomp Require Import boot.

Definition spec_correct (f : seq nat -> seq nat) := forall (l : seq nat) (n : nat), n \in l <-> n \in (f l).

Fixpoint std (l : seq nat) : seq nat :=
  match l with
  | [::] => [::]
  | n :: ns => if n \in ns then std ns else n :: (std ns) end.

Theorem std_correct : spec_correct std.
Proof.
elim=> [//| m ms IHn /=] n; rewrite in_cons.
case: ifP; case: (boolP (n == m))=> [/eqP-> | neq_mn] /=.
- by move=> /IHn.
- by move=> _; apply IHn.
- by rewrite in_cons eqxx.
- by rewrite in_cons (negPf neq_mn)=> _; apply IHn.
Qed.
