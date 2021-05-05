From CoindSemWhile Require Import SsrExport Trace Language Assert AssertClassical.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive semax : assertS -> stmt -> assertT -> Prop :=

| semax_skip: forall u, semax u Sskip ([|u|])

| semax_assign: forall u x a, semax u (Sassign x a) (Updt u x a)

| semax_seq: forall s1 s2 u v p1 p2,
  semax u s1 (p1 *** [|v|]) ->
  semax v s2 p2 ->
  semax u (Sseq s1 s2)  (p1 *** p2)

| semax_ifthenelse: forall a s1 s2 u p,
  semax (u andS eval_true a) s1 p ->
  semax (u andS eval_false a) s2 p ->
  semax u (Sifthenelse a s1 s2) (<< u >> *** p)

| semax_while: forall a s u u0 p,
  u0 ->> u ->
  semax  (u andS eval_true a) s (p *** [|u|]) ->
  semax u0 (Swhile a s) (<<u0>> *** (Iter (p *** <<u>>)) *** [|eval_false a|])

| semax_conseq: forall s u1 u2 p1 p2,
  u1 ->> u2 ->
  p2 =>> p1 ->
  semax u2 s p2 ->
  semax u1 s p1

| semax_ex: forall s (A: Type) (u: A -> assertS) (p: A -> assertT),
  (forall x, semax (u x) s (p x)) ->
  semax (exS u) s (exT p).

Lemma semax_conseq_R: forall u s p q,
p =>> q -> semax u s p -> semax u s q.
Proof.
move => u s p q h0 h1.
by apply: (semax_conseq (@assertS_imp_refl u) h0 h1).
Qed.

Lemma semax_conseq_L: forall u v s p,
v ->> u -> semax u s p -> semax v s p.
Proof.
move => u v s p h0 h1.
by apply: (semax_conseq h0 _ h1).
Qed.

(* Lemma 3.5 *)
Lemma push_pre: forall u s p, semax u s p -> semax u s ([|u|] *** p).
Proof.
have: forall u s p, semax u s p -> forall v, semax (u andS v) s ([|v|] *** p).
induction 1.
- move=>v; apply: (semax_conseq_R _ (semax_skip _)).
  move=>tr0 /= [st0 [h0 h1]]. inv h1. exists (Tnil st0).
  move: h0=>[h0 h1]. split.
  - exists st0. split=>//. apply: bisim_reflexive.
  apply follows_nil => //. exists st0. split => //. apply bisim_reflexive.
- move => v. apply: (semax_conseq_R _ (semax_assign _ _ _)).
  move => tr0 /= [st0 [h0 h1]]. inv h1. inv H1.
  move: h0=>[h0 h1]. exists (Tnil st0). split.
  - exists st0. split => //. apply bisim_reflexive.
  apply follows_nil => //. exists st0. split => //.
  apply bisim_reflexive.
- move => v0. have hs1 := IHsemax1 v0 => {IHsemax1}.
  have hs2 := IHsemax2 v => {IHsemax2}.
  move: (semax_conseq_R (@Append_assoc_R _ _ _) hs1) => {}hs1.
  apply: (semax_conseq_R _ (semax_seq hs1 (semax_conseq_L _ hs2))).
  - apply: (assertT_imp_trans _ (@Append_assoc_L _ _ _)).
    apply Append_monotone_R. apply Singleton_Append.
  by move => st0 h0.
- move => v. have hs1 := IHsemax1 v => {IHsemax1}.
  have h0: ((u andS v) andS eval_true a) ->> ((u andS eval_true a) andS v)
    by move => st0 [[h0 h1] h2].
  move: (semax_conseq_L h0 hs1) => {}hs1.
  have hs2 := IHsemax2 v => {IHsemax2}. clear h0.
  have h0: ((u andS v) andS eval_false a) ->> ((u andS eval_false a) andS v)
   by move => st0 [[h0 h1] h2].
  move: (semax_conseq_L h0 hs2) => {}hs2.
  move: (semax_ifthenelse hs1 hs2) => {h0 hs1 hs2}h.
  apply: (semax_conseq_R _ h).
  apply: (assertT_imp_trans (@Append_assoc_R _ _ _)).
  apply: (assertT_imp_trans _ (@Append_assoc_L _ _ _)).
  apply: Append_monotone_L => tr0 /= [tr1 [h0 h1]].
  move: h0 => [st0 [h0 h2]]. inv h2. inv H3. move: h0 => [h0 h2].
  inv h1. inv H4. destruct H3 as [st0 [h1 h3]]. inv h3. simpl in h0. simpl in h2.
  simpl. exists (Tnil st0). split. exists st0; split => //. apply bisim_reflexive.
  apply follows_nil => //. exists st0. split => //. apply bisim_reflexive.
- move => v.
  move: (IHsemax ttS) => {IHsemax}hs.
  have hpre: (u andS eval_true a) ->> (u andS eval_true a) andS ttS
    by move => st0 [h0 h1]; split.
  move: (semax_conseq_L hpre hs) => {hpre}hs.
  move: (semax_conseq_R (@ttS_Chop _) hs) => {}hs.
  apply: (semax_conseq_R _ (semax_while _ hs)).
  * apply: (assertT_imp_trans _ (@Append_assoc_L _ _ _)).
    apply: Append_monotone_L => tr0 [st0 [[h0 h2] h1]].
    inv h1. inv H3. simpl. exists (Tnil st0). split.
    + exists st0. split => //. apply bisim_reflexive.
    apply follows_nil => //. exists st0. split => //.
    apply bisim_reflexive.
  move => st0 [h0 h1]. by apply: H.
- move => v. have hs := IHsemax v => {IHsemax}.
  apply: (semax_conseq _ _ hs).
  * move => st0 [h0 h1]. split => //. by apply: H.
  by apply Append_monotone_R.
- move => v. have hpre: (exS u andS v) ->> exS (fun x => u x andS v).
  * move => st0 [h0 h1]. destruct h0 as [x h0]. by exists x.
  have hpost: (exT (fun x => [|v|] *** p x)) =>> ([|v|] *** exT p).
  * move => tr0 [x h0]. move hp: (p x) => px. rewrite hp in h0.
    destruct px as [q hq]. simpl in h0. destruct h0 as [tr1 [h0 h1]].
    destruct h0 as [st0 [h0 h2]]. inv h2. inv h1. simpl.
    exists (Tnil (hd tr0)). split.
    + exists (hd tr0). split => //.  apply bisim_reflexive.
    apply follows_nil => //. exists x. by rewrite hp.
  apply: (semax_conseq hpre hpost). apply semax_ex.
  clear hpre hpost. move => x. by apply: H0.
move => h u s p hs. move: (h _ _ _ hs) => {}hs.
by apply: (semax_conseq_L _ (hs _)).
Qed.
