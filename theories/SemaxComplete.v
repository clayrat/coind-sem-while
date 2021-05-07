From CoindSemWhile Require Import SsrExport Trace Language BigRel Assert Semax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Lemma 3.3 *)
Lemma conv_follows: forall (u:assertS) tr,
 (forall st, fin tr st -> u st) ->
 follows (singleton u) tr tr.
Proof.
move => u. cofix CIH. case=> st0.
- move => h0.
  apply/follows_nil/mk_singleton_nil=>//.
  by apply/h0/fin_nil.
- move => tr0 h0.
  apply/follows_delay/CIH=>st1 h1.
  by apply/h0/fin_delay.
Qed.

Lemma last_adequate: forall (p: trace -> Prop) tr, p tr ->
 (append p (singleton (last p))) tr.
Proof.
move => p tr0 /= h1. exists tr0.
split => //. apply: conv_follows=> st0 h2. by exists tr0.
Qed.

Lemma Last_adequate: forall (p: assertT),
 p =>> (p *** [| Last p |]).
Proof.
move => [f hf] tr0 /= h0.
by apply: last_adequate.
Qed.

Inductive loopinv (a: expr) (sp: assertS -> trace -> Prop) (u:assertS) : assertS :=
| loopinv_here: forall  st,
  u st ->
  loopinv a sp u st
| loopinv_next: forall st tr st' (v: assertS),
  loopinv a sp u st ->
  is_true (a st) ->
  hd tr = st ->
  (forall st, v st -> loopinv a sp u st) ->
  sp v tr ->
  fin tr st' ->
  loopinv a sp u st'.

Fixpoint sp (s: stmt) (u: assertS) {struct s} : trace -> Prop :=
match s with
| Sskip => singleton u
| Sassign x a => updt u x a
| Sseq s1 s2 =>
   append (sp s1 u) (sp s2 (last (sp s1 u)))
| Sifthenelse a s1 s2 =>
  append (dup u)
  (fun tr => sp s1 (u andS eval_true a) tr \/ sp s2 (u andS eval_false a) tr)
| Swhile a s =>
  let I := loopinv a (sp s) u in
  append (dup u)
  (append
   (iter (append (sp s (I andS eval_true a)) (dup I)))
   (singleton (eval_false a)))
end.

Lemma loopinv_init: forall u e sp, u ->> loopinv e sp u.
Proof.
move => u a sp0 st h1. by apply: loopinv_here.
Qed.

(* Lemma 3.8 *)
Lemma sp_hd: forall s u tr, sp s u tr -> u (hd tr).
Proof.
move => s; induction s => /= u tr.
- move => [st [h1 h2]]. by inv h2.
- move => [st0 [h1 h2]]. inv h2. by inv H1.
- move => [tr0 [h1 h2]].
  move: (IHs1 _ _ h1); by rewrite (follows_hd h2).
- move => [tr0 [[st1 [h1 h3]] h2]]. inv h3. inv H1. by inv h2.
- move => [tr0 [[st1 [h1 h3]] h2]]. inv h3. inv H1. by inv h2.
Qed.

Lemma loopinv_cont: forall e (sp: assertS -> trace -> Prop),
  (forall u u', u ->> u' -> forall tr, sp u tr -> sp u' tr) ->
  forall u u',  u ->> u' -> loopinv e sp u ->> loopinv e sp u'.
Proof.
move => e sp0 hsp0. rewrite /assertS_imp in hsp0 *.
move => u u' h1. induction 1.
- by apply/loopinv_here/h1.
- by apply/(loopinv_next IHloopinv)/H5/H4.
Qed.

(* Lemma 3.7: sp is monotone. *)
Lemma sp_cont: forall s u u',
 u ->> u' -> forall tr, sp s u tr -> sp s u' tr.
Proof.
move => s; induction s => /= u0 u1 h1 tr0 h2 /=.
- move: h2 => [st1 [h2 h3]]. inv h3. by apply/mk_singleton_nil/h1.
- move: h2 => [st0 [h3 h2]]. inv h2. inv H1. by apply/mk_updt/h1.
- move: h2 => [tr1 [h3 h4]]. exists tr1. split.
  * by apply: (IHs1 _ _ h1 _ h3).
  * clear h3. move: tr1 tr0 h4. cofix CIH=> tr0 tr1 h2.
    inv h2.
    - apply: follows_nil=>//.
      apply: IHs2 _ _ _ _ H0. by apply/last_cont/(IHs1 _ _ h1).
    - by apply/follows_delay/CIH/H.
- move: h2 => [tr1 [[st0 [h2 h4]] h3]].
  inv h4. inv h3. inv H1. inv H3.
  exists (Tcons (hd tr') (Tnil (hd tr'))). split; first by apply/mk_dup/h1.
  apply/follows_delay/follows_nil=>//.
  case: H1 => h6.
  - left. apply: IHs1 h6 => st0 [h6 h7].
    split=>//; by apply: h1 h6.
  - right. apply: IHs2 h6 => st0 [h6 h7].
    split=>//; by apply: h1 h6.
- move: h2 => [tr1 [[st0 [h2 h4]] h3]].
  inv h4. inv h3. inv H1. inv H3.
  exists (Tcons (hd tr') (Tnil (hd tr'))). split; first by apply/mk_dup/h1.
  apply/follows_delay/follows_nil=>//.
  have h3 := loopinv_cont IHs h1.
  have h4 := h3 e => {h3}.
  have h3: (loopinv e (sp s) u0 andS eval_true e) ->>
           (loopinv e (sp s) u1 andS eval_true e)
    by move => st0 [h0 h3]; split => //; apply: h4.
  apply/append_cont_L/H1/iter_cont/append_cont; last by apply: dup_cont h4.
  by apply: IHs.
Qed.

(* Lemma 3.11: any trace satisfying sp(s,U) is produced by a run of s. *)
Lemma sp_then_exec: forall s u tr,
sp s u  tr ->
exec s (hd tr) tr.
Proof.
move => s; induction s =>/=.
- move => u tr [st [h1 h2]]. inv h2=>/=. by apply: exec_skip.
- move => u tr [st [h1 h2]]. inv h2. inv H1=>/=. apply: exec_assign.
- move => u tr [tr0 [h1 h2]].
  have h3:= IHs1 _ _ h1.
  have h4 := follows_hd h2.
  rewrite h4 in h3.
  apply: (exec_seq h3) => {h1 h4 h3}.
  move: tr0 tr h2. cofix CIH=> tr0 tr1 h1. inv h1.
  - by apply/execseq_nil/IHs2/H0.
  - by apply/execseq_cons/CIH.
- move => u tr [tr0 [[st0 [h1 h3]] h2]].
  inv h3. inv h2. inv H1. inv H3=>/=. case: H1 => h4.
  - move: (sp_hd h4) => [h5 h6].
    apply: (exec_ifthenelse_true _ h6).
    by apply/execseq_cons/execseq_nil/IHs1/h4.
  - move: (sp_hd h4) => [h5 h6].
    apply: (exec_ifthenelse_false _ h6).
    by apply/execseq_cons/execseq_nil/IHs2/h4.
- move => u tr0 [tr1 [[st0 [h1 h3]] h2]].
  inv h3. inv H1. inv h2. inv H2=>/= {h1}.
  move: H1 => [tr0 [h0 h1]]. move: tr' tr0 h0 h1. cofix CIH.
  have h: forall tr2 tr tr1 tr0: trace, follows (dup (loopinv e (sp s) u)) tr2 tr ->
    follows (iter (append (sp s (loopinv e (sp s) u andS eval_true e))
                  (dup (loopinv e (sp s) u)))) tr tr1 ->
    follows (singleton (eval_false e)) tr1 tr0 -> execseq (Swhile e s) tr2 tr0.
  * cofix CIH0=> tr0 tr1 tr2 tr3 h0 h2 h3.
    inv h0. move: H0 => [st0 [_ h1]].
    inv h1. inv H1. inv h2. inv H2. inv h3=>/=.
    rewrite (follows_hd H3).
    apply/execseq_nil/(CIH _ _ H1 H3).
    inv h2. inv h3.
    by apply: (execseq_cons st (CIH0 _ _ _ _ H H3 H4)).
  * move => tr0 tr1 h0 h1. inv h0.
    - inv h1. move: H1 => [st0 [h0 h1]]. inv h1. simpl.
      inv h0. by apply: (exec_while_false _ H0).
    - move: H => [tr2 [h0 h2]].
      have [_ h4]:= sp_hd h0.
      have h3 := IHs _ _ h0 => {IHs h0}.
      rewrite -(follows_hd h1) -(follows_hd H0) -(follows_hd h2).
      have h5: execseq s (Tcons (hd tr2) (Tnil (hd tr2))) (Tcons (hd tr2) tr2)
        by apply/execseq_cons/execseq_nil.
      apply: (exec_while_loop h4 h5) => {h4 h5 h3}.
      by apply: (execseq_cons (hd tr2) (h _ _ _ _ h2 H0 h1)).
Qed.

(* Lemma 3.6: sp is setoid. *)
Lemma sp_setoid: forall s u tr tr',
  sp s u tr -> bisim tr tr' -> sp s u tr'.
Proof.
move => s; induction s => /= u tr0 tr1.
- move => [st0 [h1 h2]] h3. inv h2. inv h3.
  by exact: mk_singleton_nil.
- move => [st0 [h1 h2]] h3. inv h2. inv H1. inv h3. inv H2.
  by exact: mk_updt.
- move => [tr2 [h1 h2]] h3. exists tr2. split.
  * apply: (IHs1 _ _ _ h1). by apply: bisim_reflexive.
  * move => {h1}. move: tr0 tr1 tr2 h3 h2. cofix CIH=> tr0 tr1 tr2 h3 h2. inv h2.
    - apply: follows_nil; first by apply/esym/(bisim_hd h3).
      by apply: (IHs2 _ _ _ H0).
    - inv h3. by apply: (follows_delay st (CIH _ _ _ H3 H)).
- move => [tr2 [[st0 [h1 h4]] h2]] h3. inv h4.
  inv H1. inv h2. inv h3. inv H2.
  have h2 := bisim_hd H3.
  exists (Tcons (hd tr') (Tnil (hd tr'))). split; first by exact: mk_dup.
  apply/follows_delay/follows_nil; first by apply/esym.
  clear h1 h2. case: H1 => h1.
  - left. apply: (IHs1 _ _ _ h1 H3).
  - right. apply: (IHs2 _ _ _ h1 H3).
- move => [tr2 [h0 h2]] h1. exists tr2.
  split=>//. move: h0 => [st0 [h0 h3]]. inv h3. inv H1.
  inv h2. inv H2. inv h1.
  apply/follows_delay/follows_nil; first by apply/esym/(bisim_hd H3).
  by apply/(append_setoid _ H1 H3)/singleton_setoid.
Qed.

(* Lemma 3.9: => *)
Lemma loopinv_adequate: forall a s u tr,
  sp s (loopinv a (sp s) u andS eval_true a) tr ->
  append (sp s (loopinv a (sp s) u andS eval_true a))
               (singleton (loopinv a (sp s) u)) tr.
Proof.
move => a s u tr h0. exists tr. split=>//.
apply: conv_follows => st0 h1.
move: (sp_hd h0) => [h2 h3]. rewrite /is_true in h3.
have h4 := @andS_left (loopinv a (sp s) u) (eval_true a).
have h5 := sp_cont h4 h0 => {h4 h0}.
by apply: (loopinv_next h2 h3 _ _ h5).
Qed.

(* Lemma 3.9: <= *)
Lemma loopinv_adequate_aux: forall a s u tr,
  append (sp s (loopinv a (sp s) u andS eval_true a))
               (singleton (loopinv a (sp s) u)) tr ->
  sp s (loopinv a (sp s) u andS eval_true a) tr.
Proof.
move => a s u tr0 [tr1 [h0 h1]].
by apply/sp_setoid/follows_singleton/h1.
Qed.

Definition Sp (s: stmt) (u: assertS): assertT.
exists (sp s u).
move => tr0 h0 tr1 h1. by apply: (sp_setoid h0 h1).
Defined.

(* Lemma 3.10: sp is a postcondition w.r.t. the Hoare logic. *)
Lemma sp_deducible: forall s u, semax u s (Sp s u).
Proof.
move => s; induction s => u.
- apply/semax_conseq_R/semax_skip.
  move => tr0 [st0 [h0 h1]]. inv h1=>/=.
  by exact: mk_singleton_nil.
- apply/semax_conseq_R/semax_assign.
  move => tr0 [st0 [h0 h1]]. inv h1. inv H1=>/=.
  by exact: mk_updt.
- have h0 := IHs1 u => {IHs1}.
  have h1 := (@Last_adequate (Sp s1 u)).
  have h2 := semax_conseq_R h1 h0 => {h0 h1}.
  have h0 := IHs2 (Last (Sp s1 u)) => {IHs2}.
  have h3 := semax_seq h2 h0 => {h2 h0}.
  have h0: (Sp s1 u *** Sp s2 (Last (Sp s1 u))) =>> (Sp (s1;; s2) u).
  * move => {h3} tr0 [tr1 [h0 h1]] /=.
    by exists tr1.
  by apply: (semax_conseq_R h0 h3).
- have h1 := IHs1 (u andS eval_true e) => {IHs1}.
  have h2 := IHs2 (u andS eval_false e) => {IHs2}.
  have h3 := semax_conseq_R (@orT_left (Sp s1 (u andS eval_true e)) (Sp s2 (u andS eval_false e)))  h1 => {h1}.
  have h4 := semax_conseq_R (@orT_right (Sp s1 (u andS eval_true e)) (Sp s2 (u andS eval_false e)))  h2 => {h2}.
  have h0 := semax_ifthenelse h3 h4 => {h3 h4}.
  have h1: (<< u>> *** Sp s1 (u andS eval_true e) orT Sp s2 (u andS eval_false e)) =>>
                 (Sp (Sifthenelse e s1 s2) u).
  * move => tr0 /= [tr1 [{}h0 h1]].
    by exists tr1.
  by apply: (semax_conseq_R h1 h0).
- have h0 := IHs (loopinv e (sp s) u andS eval_true e) => {IHs}.
  have h1 := @loopinv_init u e (sp s).
  have h2: (Sp s (loopinv e (sp s) u andS eval_true e)) =>>
  (Sp s (loopinv e (sp s) u andS eval_true e) *** [| loopinv e (sp s) u |]).
  * move => tr0 /= {h1}h0. by apply: loopinv_adequate.
  have h3 := semax_conseq_R h2 h0 => {h2 h0}.
  have h0 := semax_while h1 h3 => {h1 h3}.
  have h1: (<<u>> *** Iter (Sp s (loopinv e (sp s) u andS eval_true e) ***
  << loopinv e (sp s) u>>) *** [| eval_false e|]) =>>
   (Sp (Swhile e s) u).
  * move => tr0 {}h0 /=. by apply: h0.
  by apply: (semax_conseq_R h1 h0).
Qed.

(* Corollary 3.2 *)
Lemma sp_correct: forall s (u: assertS) (p: assertT),
  (forall st tr, exec s st tr -> u st -> satisfy p tr) ->
  forall tr, sp s u tr -> satisfy p tr.
Proof.
move => s u p h1 tr h2.
apply/h1/(sp_hd h2)/sp_then_exec/h2.
Qed.

(* Proposition 3.4: Completeness *)
Lemma sp_complete: forall s (u: assertS) (p: assertT),
 (forall st tr, exec s st tr -> u st -> satisfy p tr) ->
 semax u s p.
Proof.
move => s u p h1.
have h2 := sp_deducible s u.
have h3 := sp_correct h1.
apply: (semax_conseq_R _ h2)=> tr0 /= h0.
apply: (h3 _ h0).
Qed.
