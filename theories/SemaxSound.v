From CoindSemWhile Require Import SsrExport Trace Language BigRel BigFunct Assert Semax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Proposition 3.3: Soundness *)
Lemma semax_sound : forall u s p, semax u s p ->
 forall st tr, exec s st tr -> u st -> satisfy p tr.
Proof.
induction 1 => st0 tr0 hexec hu.
- inv hexec=>/=; by exact: mk_singleton_nil.
- inv hexec=>/=. by exact: mk_updt.
- inv hexec.
  have h1 := IHsemax1 _ _ H3 hu.
  destruct p1 as [f1 hf1]. destruct p2 as [f2 hf2].
  clear H H0. simpl in IHsemax1. simpl in IHsemax2. simpl in h1. simpl.
  exists tr. split.
  * by apply/(@append_singleton f1)/h1.
  * clear st0 hu H3. move: h1 => [tr1[_ h1]].
     have h0 := follows_singleton h1.
     have h2 := follows_setoid_L h1 h0 => {h0 h1 IHsemax1 tr1}.
     move: tr tr0 h2 H6. cofix CIH=> tr0 tr1 h0 h1. inv h1.
     - inversion h0. clear H3 H1 H0. move: H2 => [st1 [h1 h2]].
        inv h2. have h2 := exec_hd H.
       by apply/follows_nil/IHsemax2/h1.
     - inv h0. by apply/follows_delay/CIH/H.
- destruct p as [f hf]. exists (Tcons st0 (Tnil st0)). inv hexec.
 * inv H7. inv H5. split; first by exact: mk_dup.
  * apply/follows_delay/follows_nil; first by exact: exec_hd H3.
    have h1: (u andS eval_true a) st0 by split.
    by apply: (IHsemax1 _ _ H3 h1).
 * inv H7. inv H5. split; first by exact: mk_dup.
   * apply/follows_delay/follows_nil; first by exact: exec_hd H3.
  * have h1: (u andS eval_false a) st0 by split.
    by apply: (IHsemax2 _ _ H3 h1).
- clear H0. destruct p as [p hp]. simpl in IHsemax. simpl.
  have h0: forall st, u st -> forall tr, exec (Swhile a s) st (Tcons st tr) ->
  (iter (append p (dup u))) tr.
  * cofix CIH0.
    have h: forall tr0 tr1, follows (singleton u) tr0 tr0 -> execseq (Swhile a s) tr0 tr1 ->
    follows (iter (append p (dup u))) (lastdup tr0) tr1.
    + cofix CIH1=>{H st0 hexec hu}tr0 tr1 h0 h1. inv h1.
      - inversion h0=>{h0 H1 H0 H3}. move: H2 => [st1 [h1 h2]]. inv h2.
        rewrite [lastdup _]trace_destr /=. inv H.
        * apply/follows_delay/follows_nil=>//. by apply iter_stop.
      - inversion H3; subst. inversion H5; subst. inversion H6; subst.
        apply/follows_delay/follows_nil.
        * rewrite -(exec_hd H1). by apply: (execseq_hd H8).
        by apply/(CIH0 _ h1)/(exec_while_loop H2 H3).
    - rewrite [lastdup _]trace_destr /=. inv h0.
      by apply: (follows_delay e (CIH1 _ _ H1 H)).
  * move => {H hexec hu}st0 h0 {}tr0 h1. inv h1.
    - by apply iter_stop.
    - inv H2. inv H6. inv H5.
      have h1: (u andS eval_true a) st0 by split.
      have h2 := IHsemax _ _ H2 h1 => {H2 h1 h0}.
      apply (@iter_loop _ (lastdup tr')).
      + exists tr'. split.
        * by apply: (@append_singleton p hp u _ h2).
        move: h2 => [tr1 [h2 h3]].
        have h0 := follows_singleton h3.
        have h1 := follows_setoid_L h3 h0 => {h3 h0}.
        by apply: (follows_dup h1).
      move: h2 => [tr1 [h2 h0]].
      have h3 := follows_singleton h0.
      have h4 := follows_setoid_L h0 h3 => {h0 h3}.
      by apply: (h _ _ h4 H3).
  have h1: forall st tr, exec (Swhile a s) st tr -> follows (singleton (eval_false a)) tr tr.
  * clear st0 tr0 hexec hu h0.
    have h1: forall tr0 tr1, execseq (Swhile a s) tr0 tr1 ->
    follows (singleton(eval_false a)) tr1 tr1.
    * cofix CIH=> tr0 tr1 h1. inv h1.
      + inv H0; first by apply/follows_delay/follows_nil/mk_singleton_nil.
        inv H4. inv H6. inv H7.
        by apply: (follows_delay st (CIH _ _ H6)).
      by apply: (follows_delay e (CIH _ _ H0)).
    move => st0 tr0 h0.
    inv h0; first by apply/follows_delay/follows_nil/mk_singleton_nil.
    by apply: (h1 _ _ H6).
  inversion hexec; subst.
  - exists (Tcons st0 (Tnil st0)). split; first by exact: mk_dup.
    apply/follows_delay/follows_nil => //.
    exists (Tnil st0). split; first by apply: iter_stop.
    by apply/follows_nil/mk_singleton_nil.
  - inversion H3; subst. inversion H7; subst. inversion H6; subst.
    exists (Tcons st0 (Tnil st0)). split; first by exact: mk_dup.
    apply/follows_delay/follows_nil => //.
    * rewrite -(exec_hd H4). by apply: (execseq_hd H9).
    exists tr'0. split.
    * by apply: (h0 _ (H _ hu) _ hexec).
    have h2 := h1 _ _ hexec. by inv h2.
- by apply: (H0 _ (IHsemax _ _ hexec (H _ hu))).
- move: hu => [x h0]. exists x.
  by apply: (H0 _ _ _ hexec h0).
Qed.

(* Corollary 3.1 *)
Lemma semax_total : forall S U P, semax U S P ->
 forall s, U s -> exists tr, hd tr = s /\ satisfy P tr.
Proof.
move => S U P hsemax s hU.
exists (Exec S s). split; first by apply: Exec_hd.
by exact: (semax_sound hsemax (Exec_correct_exec _ _) hU).
Qed.
