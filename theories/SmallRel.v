From CoindSemWhile Require Import SsrExport Trace Language BigRel.
From Coq Require Import JMeq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* terminality predicate*)
Inductive stop: stmt -> Prop :=
| stop_skip: stop Sskip
| stop_seq: forall s1 s2,
  stop s1 -> stop s2 -> stop (Sseq s1 s2)
(* one-step reduction relation *)
with step : stmt -> state -> stmt -> state -> Prop :=
| step_assign: forall x a st,
  step (Sassign x a) st Sskip (update x (a st) st)
| step_seq1: forall s1 s1' st' s2 st,
  step s1 st s1' st' ->
  step (Sseq s1 s2) st (Sseq s1' s2) st'
| step_seq2: forall s1 s2 s2' st st',
  stop s1 ->
  step s2 st s2' st' -> step (Sseq s1 s2) st s2' st'
| step_ifthenelse_true: forall st a s1 s2,
  is_true (a st) ->
  step (Sifthenelse a s1 s2) st s1 st
| step_ifthenelse_false: forall st a s1 s2,
  ~~ is_true (a st) ->
  step (Sifthenelse a s1 s2) st s2 st
| step_while_false: forall st a s,
  ~~ is_true (a st) ->
  step (Swhile a s) st Sskip st
| step_while_true: forall st a s,
  is_true (a st) ->
  step (Swhile a s) st (Sseq s (Swhile a s)) st.

(* small-step relational semantics *)
CoInductive redm: stmt -> state -> trace -> Prop :=
| redm_stop: forall s st,
  stop s -> redm s st (Tnil st)
| redm_step: forall s st s' st' tr,
  step s st s' st' ->
  redm s' st' tr ->
  redm s st (Tcons st tr).

Lemma stop_step_exclusive: forall s st s' st',
stop s -> step s st s' st' -> False.
Proof.
move => s; induction s => st s' st' /= h1 h2.
- by inversion h2.
- by inversion h1.
- inv h1. inv h2.
  - by apply: (IHs1 _ _ _ H1 H6).
  - by apply: (IHs2 _ _ _ H2 H7).
- by inversion h1.
- by inversion h1.
Qed.

Lemma step_deterministic: forall s st s1 st1 s2 st2,
step s st s1 st1 -> step s st s2 st2 -> s1 = s2 /\ st1 = st2.
Proof.
move => s; induction s=> st s3 st1 s4 st2 h1 h2; inv h1; inv h2=>//.
- by move: (IHs1 _ _ _ _ _ H4 H5); case=>->->.
- by move: (stop_step_exclusive H1 H4).
- by move: (stop_step_exclusive H1 H6).
- by move: (IHs2 _ _ _ _ _ H5 H7).
- by rewrite H5 in H6.
- by rewrite H6 in H5.
- by rewrite H5 in H4.
- by rewrite H4 in H5.
Qed.

(* determinism *)
Lemma redm_deterministic:
forall st s tr1 tr2, redm st s tr1 -> redm st s tr2 ->
bisim tr1 tr2.
Proof.
cofix CIH=> st s tr1 tr2 h1 h2. inv h1.
- inv h2.
  - by apply: bisim_nil.
  - by move: (stop_step_exclusive H H0).
- inv h2.
  - by move: (stop_step_exclusive H1 H).
  - have h3 := step_deterministic H H1. inv h3.
    by apply/bisim_cons/(CIH _ _ _ _ H0).
Qed.

(* setoid *)
Lemma redm_insensitive:
forall s st tr1 tr2, redm s st tr1 -> bisim tr1 tr2 ->
redm s st tr2.
Proof.
cofix CIH=> st s tr1 tr2 h1 h2. inv h1.
- inv h2. by apply: (redm_stop _ H).
- inv h2. by apply/redm_step/(CIH _ _ _  _ H0).
Qed.

Lemma red_exec:
forall s st tr, exec s st tr ->
(stop s /\ tr = Tnil st) \/ (exists s' st' tr', (step s st s' st' /\ bisim tr (Tcons st tr')) /\ exec s' st' tr').
Proof.
move => s; induction s=> st tr1 h1; inv h1.
- left. split=>//.
  by apply: stop_skip.
- right. exists Sskip, (update i (e st) st), (Tnil (update i (e st) st)). split.
  * by split; [apply: step_assign|apply: bisim_reflexive].
  * by apply: exec_skip.
- have [h2 | h2]:= IHs1 _ _ H1 => {IHs1}.
  - move: h2 => [h3 h4]. subst. inv H4.
    have [h4 | h4] := IHs2 _ _ H2 => {IHs2}.
    - move: h4 => [h5 h6]. subst. left. split=>//.
      by apply: (stop_seq h3 h5).
    - move: h4 => [s3][st1][tr2][[h5 h6] h7]. inv h6.
      right. exists s3, st1, tr2. split.
      * split.
        * by apply: (step_seq2 h3 h5).
        * by apply: (bisim_cons st H3).
      * by apply: h7.
  - right. move: h2 => [s3][st1][tr2][[h3 h4] h5]. inv h4. inv H4.
    exists (Sseq s3 s2), st1, tr'. split.
    * split.
      * by apply: (step_seq1 _ h3).
      * by apply: bisim_reflexive.
    *  apply: (exec_seq h5). by apply: (execseq_insensitive_pre H2 H6).
- inv H5. inv H3. have [h1 | h1] := IHs1 _ _ H1 => {IHs1}.
  - move: h1 => [h2 ?]. subst. right. exists s1, st, (Tnil st). split.
    * split.
      *  by apply: (step_ifthenelse_true _ _ H4).
      * by apply: bisim_reflexive.
    * by apply: H1.
  - move: h1 => [s3][st1][tr2][[h2 h3] h4]. right. inv h3.
    exists s1, st, (Tcons st tr). split.
    * split.
      * by apply: (step_ifthenelse_true _ _ H4).
      * by apply: bisim_reflexive.
    * by apply: H1.
- inv H5. inv H3. have [h1 | h1] := IHs2 _ _ H1=> {IHs1 IHs2}.
  - move: h1 => [h2 h3]. subst. right. exists s2, st, (Tnil st). split.
    * split.
      * by apply: (step_ifthenelse_false _ _ H4).
      * by apply: bisim_reflexive.
    * by apply: H1.
  - move: h1 => [s3 [st1 [tr1 h2]]]. move: h2 => [[h2 h3] h4]. inv h3. right.
    exists s2, st, (Tcons st tr). split.
    * split.
      * by apply: (step_ifthenelse_false _ _ H4).
      * by apply: bisim_reflexive.
    * by apply: H1.
- right. exists Sskip, st, (Tnil st). split.
  * split.
    * by apply: (step_while_false _ H3).
    * by apply: bisim_reflexive.
  * by apply: exec_skip.
- right. exists (Sseq s (Swhile e s)), st. inv H2. inv H5. exists tr'0. split.
  * split.
    * by apply: (step_while_true _ H1).
    * by apply: bisim_reflexive.
  * inv H6. by apply: (exec_seq H2 H4).
Qed.

(* the big-step relational semantics correct wrt the small-step relational semantis *)
Lemma exec_correct_redm: forall s st tr,
exec s st tr -> redm s st tr.
Proof.
cofix CIH=> s st tr h1. have [h2 | h2] := red_exec h1.
- move: h2 => [h3 ->]. by apply: (redm_stop _ h3).
- move: h2 => [s1][st1][tr1][[h3 h4] h5]. inv h4.
  apply: (redm_step h3). apply: CIH.
  by apply: (exec_insensitive h5 (bisim_symmetric H1)).
Qed.

CoInductive midpoint (s1 s2: stmt) (st: state) (tr: trace)
 (h: redm (Sseq s1 s2) st tr) : trace -> Prop :=
| midpoint_stop_seq : stop (s1;; s2) -> midpoint h (Tnil st)
| midpoint_stop_s1 : forall s' st' tr0,
   redm s' st' tr0 -> stop s1 -> step s2 st s' st' ->
   midpoint h (Tnil st)
| midpoint_more : forall s1' st' tr0 (h': redm (s1';; s2) st' tr0) tr',
    step s1 st s1' st' ->
    @midpoint s1' s2 st' tr0 h' tr' ->
    midpoint h (Tcons st tr').

Lemma midpoint_before0: forall s st tr tr' (h: redm s st tr),
forall s1 s2, s = Sseq s1 s2 ->
forall (h1: redm (Sseq s1 s2) st tr),
JMeq h h1 ->
midpoint h1 tr' ->
redm s1 st tr'.
Proof.
cofix CIH. dependent inversion h; subst; move => s2 s3.
- move => h1 h2. subst. move => h3. have h4 := JMeq_eq h3. rewrite -h4.
  inversion s1; subst.
  move => hm. inv hm.
  * by apply redm_stop.
  * by apply stop_step_exclusive in H3.
  * by apply stop_step_exclusive in H.
- move: s st s' st' s1 r h. dependent inversion s1; subst.
  * move => h1 h2 h3. by inversion h3.
  * move => h1 h2 h3 h4 h5. inv h3. have h6 := JMeq_eq h5.
    rewrite -h6 {h5 h6}.
    move => hm. inv hm.
    * inv H.
      by apply stop_step_exclusive in s5.
    * by apply stop_step_exclusive in s5.
    * have Heq: s1'0 = s1' /\ st'0 = st' by apply: step_deterministic; eauto.
      case: Heq => [s10 st0].
      subst.
      apply: (redm_step s5).
      have hje: JMeq h' h' by apply JMeq_refl.
      move: hje H0.
      exact: CIH.
  - move => h1 h2 h3 h4 h5. inv h3. have h6 := JMeq_eq h5. rewrite -h6 {h5 h6}.
    move => hm. inv hm.
    * inv H.
      by apply stop_step_exclusive in s6.
    * by apply (redm_stop _ s5).
    * by apply stop_step_exclusive in H.
  - move => h1 h2 h3. by inversion h3.
  - move => h1 h2 h3. by inversion h3.
  - move => h1 h2 h3. by inversion h3.
  - move => h1 h2 h3. by inversion h3.
Qed.

Lemma midpoint_before: forall s1 s2 st tr tr' (h: redm (Sseq s1 s2) st tr),
midpoint h tr' ->
redm s1 st tr'.
Proof.
move => s1 s2 st tr tr' h. by apply: (midpoint_before0 (refl_equal _) (JMeq_refl _)).
Qed.

CoInductive redm_str: stmt -> trace -> trace -> Prop :=
| redm_nil: forall s st tr,
  redm s st tr ->
  redm_str s (Tnil st) tr
| redm_cons: forall s tr tr' st,
  redm_str s tr tr' ->
  redm_str s (Tcons st tr) (Tcons st tr').

(*
Lemma midpoint_after0: forall s st tr (h: redm s st tr),
forall s1 s2, s = Sseq s1 s2 ->
forall (h1: redm (Sseq s1 s2) st tr),
JMeq h h1 ->
redm_str s2 (midpoint h1) tr.
Proof.
cofix CIH. dependent inversion h; subst; move => s2 s3.
- move => h1 h2. subst. move => h3. have h4 := JMeq_eq h3. rewrite -h4.
  rewrite [midpoint _]trace_destr. simpl. apply: redm_nil.
  inversion s1; subst. by apply: (redm_stop _ H2).
- move: s st s' st' s1 r h. dependent inversion s1; subst.
  - move => h1 h2 h3. by inversion h3.
  - move => h1 h2 h3 h4 h5. inv h3. have h6 := JMeq_eq h5.
    rewrite -h6. rewrite [midpoint _]trace_destr. simpl.
    by apply: (redm_cons _ (CIH _ _ _ _ _ _ (refl_equal _) _ (JMeq_refl _))).
  - move => h1 h2 h3 h4 h5. inv h3. have h6 := JMeq_eq h5. rewrite -h6.
    rewrite [midpoint _]trace_destr. simpl. apply: redm_nil.
    by apply: (redm_step s6 h1).
  - move => h1 h2 h3. by inversion h3.
  - move => h1 h2 h3. by inversion h3.
  - move => h1 h2 h3. by inversion h3.
  - move => h1 h2 h3. by inversion h3.
Qed.

Lemma midpoint_after: forall s1 s2 st tr (h: redm (Sseq s1 s2) st tr),
redm_str s2 (midpoint h) tr.
Proof.
move => s1 s2 st tr h. by apply: (midpoint_after0 (refl_equal  _ ) (JMeq_refl _)).
Qed.

(* the small-step relational semantics correct wrt the big-step relational semantics *)
Lemma redm_correct_exec: forall s st tr, redm s st tr -> exec s st tr.
Proof.
cofix CIH.
have CIH2: forall s tr1 tr2, redm_str s tr1 tr2 -> execseq s tr1 tr2.
* cofix CIH2. move => s tr1 tr2 h1. inv h1.
  - by apply: (execseq_nil (CIH _ _ _ H)).
  - by apply: (execseq_cons _ (CIH2 _ _ _ H)).
* case.
  - move => st tr h1. inv h1.
    - by apply: exec_skip.
    - by inversion H.
  - move => i a st tr h1. inv h1.
    - by inversion H.
    - inv H. inv H0.
      - by apply: exec_assign.
      - by inversion H.
  - move => s1 s2 st tr h1. have h2 := midpoint_before h1.
    have h3 := midpoint_after h1.
    by apply: (exec_seq (CIH _ _ _ h2) (CIH2 _ _ _ h3)).
  - move => a s1 s2 st tr h1. inv h1.
    - by inversion H.
    - inv H.
      - apply: (exec_ifthenelse_true _ H7).
        by apply: (execseq_cons _ (execseq_nil (CIH _ _ _ H0))).
      - apply: (exec_ifthenelse_false _ H7).
        by apply: (execseq_cons _ (execseq_nil (CIH _ _ _ H0))).
  - move => a s st tr h1. inv h1.
    - by inversion H.
    - inv H.
      - inv H0.
        - by apply: (exec_while_false _ H6).
        -  by inversion H.
      - have h2 := midpoint_before H0. have h3 := midpoint_after H0.
        apply: (exec_while_loop H6). apply execseq_cons.  apply: execseq_nil.
        apply (CIH _ _ _ h2). apply: execseq_cons. apply: (CIH2 _ _ _ h3).
Qed.
*)

(* adequacy relative to the inductive semantics *)
Inductive norm: stmt -> state -> state -> Prop :=
| norm_nil: forall s st,
  stop s  -> norm s st st
| norm_cons: forall s st s'  st' st'',
  step s st s' st' ->
  norm s' st' st'' ->
  norm s st st''.

Inductive result: trace -> state -> Prop :=
| res_return: forall st, result (Tnil st) st
| res_step: forall st st' tr,
  result tr st ->
  result (Tcons st' tr) st.

Lemma redm_correct_norm:
forall tr st, result tr st -> forall s st', redm s st' tr -> norm s st' st.
Proof.
induction 1=> s st1 h1; inv h1.
- by apply: (norm_nil _ H2).
- by apply/norm_cons/(IHresult _ _ H5).
Qed.

Lemma norm_correct_redm: forall s st st',
 norm s st st' -> exists tr, redm s st tr /\ result tr st'.
Proof.
move => s st st' h1. induction h1.
- exists (Tnil st). split.
  * by apply: (redm_stop _ _).
  * by apply: res_return.
- move: IHh1 => [tr][h2]h3. exists (Tcons st tr). split.
  * by apply: (redm_step _ h2).
  * by apply: (res_step _  h3).
Qed.
