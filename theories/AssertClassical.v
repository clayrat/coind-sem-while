From CoindSemWhile Require Import SsrExport Trace Language Assert.
From Coq Require Import ClassicalEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition follows_dec : forall p tr0 tr1 (h: follows p tr0 tr1),
 { tr & { st | tr0 = Tnil st /\ hd tr = st /\ p tr } } +
 { tr & { tr' & { st | tr0 = Tcons st tr /\ tr1 = Tcons st tr' /\ follows p tr tr'} } }.
Proof.
move=>p tr0 tr1 h.
destruct tr0.
- left; exists tr1, s. by inversion h; subst.
- destruct tr1.
  * left; exists (Tnil s0), s0. by inversion h; subst.
  * right; exists tr0, tr1, s. by inversion h; subst.
Defined.

CoFixpoint midp_dec (p0 p1: trace -> Prop) tr0 tr1 (h: follows (append p0 p1) tr0 tr1) : trace.
Proof.
case (follows_dec h).
- case => tr; case => st; case => h1; case => h2 h3.
  apply constructive_indefinite_description in h3.
  by case: h3 => x [h4 h5].
- case => tr; case => tr'; case => st; case => h1; case => h2 h3.
  by apply (Tcons st (@midp_dec _ _ _ _ h3)).
Defined.

Lemma midp_midp_dec : forall (p0 p1: trace -> Prop)  tr0 tr1 (h : follows (append p0 p1) tr0 tr1),
 midp h (midp_dec h).
Proof.
cofix CIH.
dependent inversion h.
- subst.
  intros.
  rewrite [midp_dec _]trace_destr /=.
  case (constructive_indefinite_description _ _); simpl.
  move => x [a0 hm].
  by apply midp_follows_nil => //; destruct x.
- subst.
  rewrite [midp_dec _]trace_destr /=.
  by apply (@midp_follows_delay p0 p1 (Tcons st tr) (Tcons st tr') (follows_delay st f) tr tr' f st (midp_dec f)).
Qed.

Lemma append_assoc_R: forall p1 p2 p3,
 forall tr, (append p1 (append p2 p3)) tr -> (append (append p1 p2)  p3) tr.
Proof.
move => p1 p2 p3 tr0 [tr1 [h1 h2]].
exists (midp_dec h2). split.
- exists tr1. split=>//.
  by exact: (midp_before (midp_midp_dec h2)).
- by exact: (midp_after (midp_midp_dec h2)).
Qed.

(* Lemma 3.4 (4) <= *)
Lemma Append_assoc_R: forall p1 p2 p3, (p1 *** p2 *** p3) =>> (p1 *** p2) *** p3.
Proof.
move => [f1 hf1] [f2 hf2] [f3 hf3] tr0 /= h1. by apply: append_assoc_R.
Qed.

Definition Tnil_eq_fin tr st (h : Tnil st = tr) : fin tr st.
Proof.
by rewrite -h; apply fin_nil.
Defined.

Definition Tcons_eq_fin tr tr' st st' (h : Tcons st tr' = tr) (h': fin tr' st') : fin tr st'.
Proof.
by rewrite -h; apply fin_delay.
Defined.

CoFixpoint f (q : trace -> Prop) tr
  (g: forall st, fin tr st -> {tr1 : trace | q tr1 /\ hd tr1 = st}) : trace :=
match tr as tr' return (tr' = tr -> trace) with
| Tnil st => fun h => let: exist tr1 _ := g st (Tnil_eq_fin h) in tr1
| Tcons st tr' => fun h => Tcons st (@f q tr' (fun st0 h' => g _ (Tcons_eq_fin h h')))
end eq_refl.

Lemma singleton_last_fin: forall p q tr0,
 (forall tr, singleton (last p) tr -> exists tr1, follows q tr tr1) ->
 p tr0 ->
 forall st, fin tr0 st -> { tr1 | q tr1 /\ hd tr1 = st}.
Proof.
move => p q tr0 h0 h1 st0 h2.
have h3: singleton (last p) (Tnil st0).
  by exists st0; split; last apply bisim_reflexive; exists tr0.
have := h0 _ h3 => {h0 h3} h.
move/constructive_indefinite_description: h => [tr1 h0]. exists tr1. by inv h0.
Qed.

Lemma fin_hd_follows : forall q tr0,
 (forall st, fin tr0 st -> { tr1 | q tr1 /\ hd tr1 = st }) ->
 exists tr1, follows q tr0 tr1.
Proof.
move => q tr0 h2. exists (f h2).
move: tr0 h2. cofix hcoind => t0. dependent inversion t0.
- move => h0. rewrite [f _]trace_destr /=.
  destruct (h0 s (fin_nil s)).
  destruct a.
  by destruct x; apply follows_nil.
- move => h0. rewrite [f _]trace_destr /=.
  by apply/follows_delay/hcoind.
Qed.
