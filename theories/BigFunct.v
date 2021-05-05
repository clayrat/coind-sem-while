From CoindSemWhile Require Import SsrExport Trace Language BigRel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

CoFixpoint loop (k:state -> trace) (p:state -> bool) (st: state) : trace :=
if p st then
  match k st with
  | Tnil st' => Tcons st' (loop k p st')
  | Tcons st' tr => Tcons st' (loopseq k p tr)
  end
else Tnil st

with loopseq (k:state -> trace) (p:state -> bool) (tr:trace) : trace :=
match tr with
| Tnil st => Tcons st (loop k p st)
| Tcons st tr' => Tcons st (loopseq k p tr')
end.

Lemma loop_true_nil: forall p k st,
p st = true -> k st = Tnil st -> loop k p st = Tcons st (loop k p st).
Proof.
move => p k st h1 h2.
by rewrite {1}[loop k p st]trace_destr /= h1 h2.
Qed.

Lemma loop_true_cons: forall p k st tr,
p st = true -> k st = Tcons st tr -> loop k p st = Tcons st (loopseq k p tr).
Proof.
move => p k st tr h1 h2.
by rewrite {1}[loop k p st]trace_destr /= h1 h2.
Qed.

Lemma loop_false: forall k p st, p st = false -> loop k p st = Tnil st.
Proof.
move => k p st h1.
by rewrite [loop _ _ _]trace_destr /= h1.
Qed.

Lemma loop_nil: forall k p st, loopseq k p (Tnil st) = Tcons st (loop k p st).
Proof.
move => k p st.
by rewrite {1}[loopseq _ _ _]trace_destr.
Qed.

Lemma loopseq_cons: forall k p st tr,
loopseq k p (Tcons st tr) = Tcons st (loopseq k p tr).
Proof.
move => k p st tr.
by rewrite {1}[loopseq _ _ _]trace_destr.
Qed.

CoFixpoint sequence (k: state -> trace) (tr:trace): trace :=
match tr with
| Tnil st => k st
| Tcons st tr' => Tcons st (sequence k tr')
end.

Lemma sequence_nil: forall k st, sequence k (Tnil st) = k st.
Proof.
move => k st.
by rewrite [sequence _ _]trace_destr /= {2}[k st]trace_destr /trace_decompose.
Qed.

Lemma sequence_cons: forall k st tr,
sequence k (Tcons st tr) = Tcons st (sequence k tr).
Proof.
move => k st tr.
by rewrite {1}[sequence  _ _]trace_destr /=.
Qed.

Fixpoint Exec (s:stmt) (st: state): trace :=
match s with
| Sskip => Tnil st
| Sassign id a => Tcons st (Tnil (update id (a st) st))
| Sseq s1 s2 => sequence (Exec s2) (Exec s1 st)
| Sifthenelse a s1 s2 =>
  Tcons st (if (is_true (a st)) then (Exec s1 st) else (Exec s2 st))
| Swhile a s =>
  Tcons st (loop (Exec s) (fun st0 => is_true (a st0)) st)
end.

Lemma sequence_correct0: forall s,
(forall st0, exec s st0 (Exec s st0)) ->
forall tr, execseq s tr (sequence (Exec s) tr).
Proof.
cofix COINDHYP=> s h1. case.
- move => st1. apply: execseq_nil. rewrite sequence_nil. by apply: h1.
- move => st0 tr0. rewrite sequence_cons.
  by apply/execseq_cons/COINDHYP.
Qed.

Lemma Exec_nil: forall s st1 st2, Exec s st1 = Tnil st2 -> st1 = st2.
Proof.
move => s; induction s=> st1 st2 h1.
- by inv h1.
- by inv h1.
- inv h1. case h2: (Exec s1 st1).
  - rewrite h2 in H0. rewrite sequence_nil in H0.
    rewrite (IHs1 _ _ h2); by apply: IHs2.
  - rewrite h2 in H0. rewrite sequence_cons in H0. by inversion H0.
- by inversion h1.
- by inversion h1.
Qed.

Lemma sequence_eq_nil: forall s  tr st,
sequence (Exec s) tr = Tnil st -> tr = Tnil st /\ Exec s st = Tnil st.
Proof.
move => s. case.
- move => st1 st2. rewrite sequence_nil => /[dup]/Exec_nil->. by split.
- move => st1 tr st2 h1. rewrite sequence_cons in h1. by inversion h1.
Qed.

Lemma Exec_sound_nil: forall s st st',
Exec s st = Tnil st' -> exec s st (Tnil st').
Proof.
induction s.
- move => st1 st2 /= h1. inv h1. by apply exec_skip.
- move => st1 st2 /= h1. by inversion h1.
- move => st1 st2 /= h1. move: (sequence_eq_nil h1) => [h2 h3].
  move: (IHs1 _ _ h2) => h4 {IHs1 h2}. move: (IHs2 _ _ h3) => h5 {IHs2 h3}.
  apply: (exec_seq h4). by apply (execseq_nil h5).
- move => st1 st2 h1. by inversion h1.
- move => st st1 h1. by inversion h1.
Qed.

Lemma loop_skip_correct: forall s st e,
Exec s st = Tnil st ->
is_true (e st) ->
exec (Swhile e s) st
 (Tcons st (loop (Exec s) (fun st0 => is_true (e st0)) st)).
Proof.
move => s st e h1 h2. cofix COINDHYP.
apply: (exec_while_loop h2).
- by apply/execseq_cons/execseq_nil/(Exec_sound_nil h1).
rewrite [loop _ _ _]trace_destr /= h1 h2.
by apply/execseq_cons/(execseq_nil COINDHYP).
Qed.

Lemma loop_correct0: forall  e s,
(forall st, exec s st (Exec s st)) ->
forall st, exec (Swhile e s) st
 (Tcons st (loop (Exec s) (fun st0 => is_true (e st0)) st)).
Proof.
move => e s h1. cofix COINDHYP.
have COINDHYP2: forall tr,
                execseq (Swhile e s) tr (loopseq (Exec s) (fun st0 => is_true (e st0)) tr).
* cofix COINDHYP2. case=>st1.
  - rewrite [loopseq _ _ _]trace_destr /=.
    by apply/execseq_nil/COINDHYP.
  - move => tr1. rewrite [loopseq _ _ _]trace_destr /=.
    by apply/execseq_cons/COINDHYP2.
* move => st. case/boolP: (is_true (e st))=>h2.
  - case h3: (Exec s st).
    - have h4 := (Exec_nil h3). rewrite -h4 in h3.
      by apply: (loop_skip_correct h3 h2).
    - rewrite [loop _ _ _]trace_destr /= h2 h3.
      apply: (exec_while_loop h2 (execseq_cons _  (execseq_nil (h1 _)))).
      rewrite h3.
      by apply/execseq_cons/execseq_cons/COINDHYP2.
  - rewrite [loop _ _ _]trace_destr /= (negbTE h2). by apply: (exec_while_false _ h2).
Qed.

(* the big-step functional semantics correct wrt the big-step relational semantics *)
Lemma Exec_correct_exec: forall s st, exec s st (Exec s st).
Proof.
move => s; induction s=> st /=.
- by exact: exec_skip.
- by apply: exec_assign.
- apply: exec_seq; first by apply: IHs1 st.
  by apply: sequence_correct0 IHs2 (Exec s1 st).
- case/boolP: (is_true (e st))=>h1.
  - apply: (exec_ifthenelse_true _ h1). by apply/execseq_cons/execseq_nil/IHs1.
  - apply: (exec_ifthenelse_false _ h1). by apply/execseq_cons/execseq_nil/IHs2.
- by apply: (loop_correct0 _ IHs).
Qed.

(* the big-step relational semantics correct wrt the big-step functional semantics *)
Lemma exec_correct_Exec: forall s st tr, exec s st tr -> bisim tr (Exec s st).
Proof.
move => s st tr h1.
by apply/(exec_deterministic h1)/Exec_correct_exec.
Qed.

Lemma Exec_hd : forall s st, hd (Exec s st) = st.
Proof.
elim => //= s1 IHs1 s2 IHs2 st.
case H: (Exec s1 st) => [st'|].
- move/Exec_nil: H=><-.
  by apply: IHs2.
by move: (IHs1 st); rewrite H.
Qed.
