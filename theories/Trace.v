From CoindSemWhile Require Import SsrExport.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Ltac inv h := inversion h; subst=>{h}.

Definition id := nat.
Definition val := nat.
Definition state := id -> val.

CoInductive trace : Set :=
| Tnil (_: state)
| Tcons (_: state) (_: trace).

(* AKA Chlipala's frob *)
Definition trace_decompose (tr: trace): trace :=
match tr with
| Tnil st => Tnil st
| Tcons a tr' => Tcons a tr'
end.

Lemma trace_destr:
forall tr, tr = trace_decompose tr.
Proof. by case=>/=. Qed.

(* bisimilarity of two traces *)
CoInductive bisim: trace -> trace -> Prop :=
| bisim_nil: forall st,
  bisim (Tnil st) (Tnil st)
| bisim_cons: forall e tr tr',
  bisim tr tr' ->
  bisim (Tcons e tr) (Tcons e tr').

(* Bisimilarity is reflexive *)
Lemma bisim_reflexive: forall tr, bisim tr tr.
Proof.
cofix CIH. case=>st.
- by apply: bisim_nil.
- by move=>?; apply/bisim_cons/CIH.
Qed.

(* Bisimilarity is symmetric *)
Lemma bisim_symmetric: forall tr1 tr2, bisim tr1 tr2 -> bisim tr2 tr1.
Proof.
cofix CIH. case=>s.
- move=>? h1; inv h1.
  by apply: bisim_nil.
- move=>?? h1; inv h1.
  by apply/bisim_cons/CIH.
Qed.

(* Bisimilarity is transitive *)
Lemma bisim_transitive: forall tr1 tr2 tr3,
bisim tr1 tr2 -> bisim tr2 tr3 -> bisim tr1 tr3.
Proof.
cofix CIH. case=>st tr0 tr1.
- move=>h1 h2; inv h1; inv h2.
  by apply: bisim_nil.
- move=>? h1 h2; inv h1; inv h2.
  by apply/bisim_cons/(CIH _ _ _ H2).
Qed.


CoFixpoint trace_append (tr tr': trace): trace :=
match tr with
| Tnil st => tr'
| Tcons e tr0 => Tcons e (trace_append tr0 tr')
end.

Infix "+++" := trace_append (at level 60, right associativity).

Lemma trace_append_nil: forall st tr,
(Tnil st) +++ tr = tr.
Proof.
move=>st tr.
rewrite [Tnil st +++ tr]trace_destr.
by case: tr=>/=.
Qed.

Lemma trace_append_cons: forall e tr tr',
(Tcons e tr) +++ tr' = Tcons e (tr +++ tr').
Proof.
move=>st tr tr'.
rewrite [Tcons st tr +++ tr']trace_destr.
by case: tr=>/=.
Qed.

Lemma trace_eq_append: forall tr1 tr2 tr3 tr4,
bisim tr1 tr2 -> bisim tr3 tr4 -> bisim (tr1 +++ tr3) (tr2 +++ tr4).
Proof.
cofix CIH. case=>st1 tr1 tr2 tr3.
- move=>h1 h2; inv h1.
  by rewrite 2!trace_append_nil.
- move=>tr4 h1 h2; inv h1.
  rewrite 2!trace_append_cons.
  by apply/bisim_cons/CIH.
Qed.

Definition hd tr := match tr with Tnil st => st | Tcons st tr0 => st end.

Lemma bisim_hd: forall tr0 tr1, bisim tr0 tr1 -> hd tr0 = hd tr1.
Proof.
move=>?? h0.
by inv h0=>/=.
Qed.
