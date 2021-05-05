From CoindSemWhile Require Import SsrExport Trace Language SmallRel BigRel BigFunct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* one-step reduction function *)
Fixpoint red (s: stmt) (st: state) {struct s}: option (stmt * state) :=
match s with
| Sskip => None
| (Sassign x a) => Some (Sskip, update x (a st) st)
| (Sseq s1 s2) =>
  match red s1 st with
  | Some (s1', st') => Some (Sseq s1' s2, st')
  | None => red s2 st
  end
| (Sifthenelse a s1 s2) =>
  if is_true (a st) then Some (s1, st) else Some (s2, st)
| (Swhile a s) =>
  if is_true (a st)  then Some (Sseq s (Swhile a s), st)
  else Some (Sskip, st)
end.

(* small-step functional semantics *)
CoFixpoint Redm (s: stmt) (st: state): trace :=
match red s st with
| None => Tnil st
| Some (s', st') => Tcons st (Redm s' st')
end.

Lemma red_then_stop: forall s st,
red s st = None -> stop s.
Proof.
move=>s; induction s=>st h1.
- by apply: stop_skip.
- by inversion h1.
- inv h1. case h2: (red s1 st) =>[[??]|]; rewrite h2 // in H0.
  by apply: (stop_seq (IHs1 _ h2) (IHs2 _ H0)).
- inv h1. move: H0. by case: (is_true (e st)).
- inv h1. move: H0. by case: (is_true (e st)).
Qed.

Lemma red_then_step: forall s st s' st',
red s st = Some (s', st') -> step s st s' st'.
Proof.
move => s; induction s.
- move => st s st' h1. by inversion h1.
- move => st s st' h1. inv h1. by apply step_assign.
- move => st1 s3 st2 h1. case h2 : (red s1 st1)=> [[s1' st1']|].
  - inv h1. rewrite h2 in H0. inv H0.
    by apply/step_seq1/IHs1.
  - inv h1. rewrite h2 in H0.
    by apply: (step_seq2 (red_then_stop h2) (IHs2 _ _ _ H0)).
- move => st1 s3 st2 /= h1. case/boolP: (is_true (e st1))=>h2.
  - rewrite h2 in h1. inv h1.
    by apply: step_ifthenelse_true.
  - rewrite (negbTE h2) in h1. inv h1.
    by apply: step_ifthenelse_false.
- move => st s' st' /= h1. case/boolP: (is_true (e st)) => h2.
  - rewrite h2 in h1. inv h1.
    by apply: step_while_true.
  - rewrite (negbTE h2) in h1. inv h1.
    by apply: step_while_false.
Qed.

Lemma stop_then_red: forall s st, stop s -> red s st = None.
Proof.
induction 1=>//=.
by rewrite IHstop1.
Qed.

Lemma step_then_red: forall s st s' st',
step s st s' st' -> red s st = Some (s', st').
Proof.
induction 1=>//=.
- by rewrite IHstep.
- by rewrite (stop_then_red st H) IHstep.
- by rewrite H.
- by rewrite (negbTE H).
- by rewrite (negbTE H).
- by rewrite H.
Qed.

(* the small-step functional semantics correct wrt the small-step relational semantics. *)
Lemma Redm_correct_redm: forall st s, redm s st (Redm s st).
Proof.
cofix COINDHYP=>st s. rewrite [Redm s st]trace_destr /=.
case h1: (red s st) => [[s' st'] /=|].
- have h2 := red_then_step h1.
  by apply/(redm_step h2)/COINDHYP.
- by apply/redm_stop/(red_then_stop h1).
Qed.

(* the small-step relational semantics correct wrt the small-step functional semantics *)
Lemma redm_correct_Redm: forall s st tr, redm s st tr -> bisim tr (Redm s st).
Proof.
move => s st tr h1.
by apply/(redm_deterministic h1)/Redm_correct_redm.
Qed.

Lemma redmseq_correct_execseq0: forall s,
(forall st tr, redm s st tr -> exec s st tr) ->
forall tr1 tr2, redm_str s tr1 tr2 ->
execseq s tr1 tr2.
Proof.
move => s h.
cofix COINDHYP => tr1 tr2 h1. inv h1.
- by apply/execseq_nil/h.
- by apply/execseq_cons/COINDHYP.
Qed.

Lemma Redm_sequence: forall s1 s2 st,
bisim (Redm (Sseq s1 s2) st) (sequence (Redm s2) (Redm s1 st)).
Proof.
cofix COINDHYP=> s1 s2 st.
rewrite [Redm (Sseq s1 s2) st]trace_destr /= [Redm s1 st]trace_destr /=.
case h1 : (red s1 st) => [[s1' st']|]; rewrite [sequence _ _]trace_destr /=.
- by apply/bisim_cons/COINDHYP.
- case: (red s2 st)=>*.
  - by apply: bisim_reflexive.
  - by apply: bisim_nil.
Qed.


Lemma sequence_deterministic0: forall k1 k2,
(forall st, bisim (k1 st) (k2 st)) ->
forall tr1 tr2, bisim tr1 tr2 ->
bisim (sequence k1 tr1) (sequence k2 tr2).
Proof.
move => k1 k2 h1.
cofix COINDHYP=> tr1 tr2 h2. inv h2.
- rewrite [sequence k1 _]trace_destr [sequence k2 _]trace_destr /=.
  have h3 := h1 st.
  by inv h3; [apply: bisim_nil|apply: bisim_cons].
- rewrite [sequence k1 _]trace_destr /= [sequence k2 _]trace_destr /=.
  by apply/bisim_cons/COINDHYP.
Qed.

Lemma Redm_loop_skip: forall a s st,
is_true (a st) = true ->
red s st = None ->
bisim (Redm (Sseq s (Swhile a s)) st)
 (loop (Redm s) (fun st0 => is_true (a st0)) st).
Proof.
move => a s st h1 h2.
cofix COINDHYP.
rewrite [Redm _ _]trace_destr /= [loop _ _ _]trace_destr /= h1 h2 /=.
by apply/bisim_cons/COINDHYP.
Qed.


Lemma Redm_loop: forall a s,
forall st, bisim (Redm (Swhile a s) st)
 (Tcons st (loop (Redm s) (fun st0 => is_true (a st0)) st)).
Proof.
cofix COINDHYP.
have COINDHYP2: forall a s s1 st1,
                bisim (Redm (Sseq s1 (Swhile a s)) st1)
                (loopseq (Redm s) (fun st0 => is_true (a st0)) (Redm s1 st1)).
* cofix COINDHYP2=> a s s1 st1. case h1: (red s1 st1) => [[s1' st1']|].
  - rewrite [loopseq _ _ _]trace_destr /= [Redm _ _]trace_destr /= h1 /=.
    by apply/bisim_cons/COINDHYP2.
  - case h2 : (is_true (a st1)).
    - rewrite [Redm _ _]trace_destr /= h1 h2 /= [loopseq _ _ _]trace_destr /= h1 /=
              [loop _ _ _]trace_destr /= h2.
      case h3 : (red s st1) => [[s' st1']|].
      - rewrite [Redm _ _]trace_destr /= h3 /=.
        by apply/bisim_cons/bisim_cons/COINDHYP2.
      - rewrite [Redm _ _]trace_destr /= h2 h3 /=.
        by apply/bisim_cons/bisim_cons/(Redm_loop_skip h2 h3).
    - rewrite [Redm _ _]trace_destr /= h1 h2 /= [loopseq _ _ _]trace_destr /= h1 /=
              [loop _ _ _]trace_destr /= h2 /= [Redm _ _]trace_destr /=.
      by apply: bisim_reflexive.
move => a s st. case h1 : (is_true (a st)).
- rewrite [Redm _ _]trace_destr /= h1 /=.
  case h2 :(red s st) => [[s' st']|].
  - rewrite [loop _ _ _]trace_destr /= h1 h2 /= [Redm _ _]trace_destr /= h2 /=.
    by apply/bisim_cons/bisim_cons/COINDHYP2.
  - by apply/bisim_cons/(Redm_loop_skip h1 h2).
- rewrite [Redm _ _]trace_destr /= h1 /= [Redm _ _]trace_destr /=
          [loop _ _ _]trace_destr /= h1 /=.
  by apply: bisim_reflexive.
Qed.

Lemma loop_deterministic0: forall k1 k2 p,
(forall st, bisim (k1 st) (k2 st)) ->
forall st, bisim (loop k1 p st) (loop k2 p st).
Proof.
move => k1 k2 p h1. cofix COINDHYP.
have COINDHYP2 : forall tr1 tr2,
                 bisim tr1 tr2 -> bisim (loopseq k1 p tr1) (loopseq k2 p tr2).
- cofix COINDHYP2=> tr1 tr2 h2. inv h2.
  - rewrite [loopseq k1 _ _]trace_destr /= [loopseq k2 _ _]trace_destr /=.
    by apply/bisim_cons/COINDHYP.
  - rewrite [loopseq k1 _ _]trace_destr /= [loopseq k2 _ _]trace_destr /=.
    by apply/bisim_cons/COINDHYP2.
* move => st. case h2: (p st).
  - have h3 := h1 st. inv h3.
    - rewrite [loop k1 _ _]trace_destr /= [loop k2 _ _]trace_destr /= h2 -H -H0.
      by apply/bisim_cons/COINDHYP.
    - rewrite [loop k1 _ _]trace_destr /= [loop k2 _ _]trace_destr /= h2 -H -H0.
      by apply/bisim_cons/COINDHYP2.
  - rewrite [loop k1 _ _]trace_destr /= [loop k2 _ _]trace_destr /= h2.
    by apply: bisim_nil.
Qed.

(* equivalence of the small-step functional semantics to the big-step functional semantics *)
Lemma Exec_Redm: forall s st, bisim (Exec s st) (Redm s st).
Proof.
move => s; induction s=>st.
- rewrite [Redm _ _]trace_destr /=. by apply: bisim_nil.
- rewrite [Redm _ _]trace_destr /= [Redm _ _]trace_destr /=.
  by apply/bisim_cons/bisim_nil.
- move => /=.
  have h1 := IHs1 st.
  have h2 := sequence_deterministic0 IHs2 h1.
  have h3 := Redm_sequence s1 s2 st.
  by apply: (bisim_transitive h2 (bisim_symmetric h3)).
- case h1: (is_true (e st)).
  - rewrite [Redm _ _]trace_destr /= h1 /=.
    by apply/bisim_cons/IHs1.
  - rewrite [Redm _ _]trace_destr /= h1 /=.
    by apply/bisim_cons/IHs2.
- move => /=.
  have h1 := Redm_loop e s st.
  have h2 := loop_deterministic0 (fun st0 => is_true (e st0)) IHs st.
  by apply/bisim_symmetric: (bisim_transitive h1 (bisim_cons _ (bisim_symmetric h2))).
Qed.

(* the small-step relational semantics correct wrt the big-step relational semantics *)
(* by going through the functional semantics *)
Lemma redm_correct_exec: forall s st tr, redm s st tr -> exec s st tr.
Proof.
move => s st tr h1.
have h2 := Redm_correct_redm st s.
have h3 := redm_deterministic h1 h2.
have h4 := Exec_Redm s st.
have h5 := Exec_correct_exec s st.
by apply: (exec_insensitive h5 (bisim_transitive h4 (bisim_symmetric h3))).
Qed.

