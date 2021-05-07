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
Proof. move => u s p q h0 h1. by apply/semax_conseq/h1. Qed.

Lemma semax_conseq_L: forall u v s p,
v ->> u -> semax u s p -> semax v s p.
Proof. move => u v s p h0 h1. by apply/semax_conseq/h1. Qed.

Lemma push_pre_andS: forall u s p, semax u s p -> forall v, semax (u andS v) s ([|v|] *** p).
induction 1=>v0.
- apply/semax_conseq_R/semax_skip.
  apply/impT_conseq_L/Sglt_Chop_2/singleton_monotone.
  by exact: andS_comm.
- apply/semax_conseq_R/semax_assign.
  move => tr0 /= [st0][[h0 h1] h2]. inv h2. inv H1.
  exists (Tnil st0). split; first by exact: mk_singleton_nil.
  by apply/follows_nil/mk_updt.
- move: (semax_conseq_R (@Append_assoc_R _ _ _) (IHsemax1 v0)) => {IHsemax1}hs1.
  apply/semax_conseq_R/(semax_seq hs1)/semax_conseq_L/IHsemax2/v=>//.
  by apply/impT_conseq_L/Append_assoc_L/Append_monotone_R/Singleton_Append.
- have h0: ((u andS v0) andS eval_true a) ->> ((u andS eval_true a) andS v0)
    by move => st0 [[h0 h1] h2].
  move: (semax_conseq_L h0 (IHsemax1 v0)) => {h0 IHsemax1}hs1.
  have h0: ((u andS v0) andS eval_false a) ->> ((u andS eval_false a) andS v0)
    by move => st0 [[h0 h1] h2].
  move: (semax_conseq_L h0 (IHsemax2 v0)) => {IHsemax2}hs2.
  move: (semax_ifthenelse hs1 hs2) => {h0 hs1 hs2}h.
  apply: (semax_conseq_R _ h).
  apply: (impT_conseq_L (@Append_assoc_R _ _ _)).
  apply/impT_conseq_L/Append_assoc_L/Append_monotone_L.
  move => tr0 /= [tr1][[st0][[h0 h2] h3] h1].
  inv h3. inv H3. inv h1. inv H4.
  destruct H3 as [st0 [h1 h3]]. inv h3. simpl in h0. simpl in h2. simpl.
  exists (Tnil st0). split; first by exact: mk_singleton_nil.
  by apply/follows_nil/mk_dup.
- apply/semax_conseq_R/semax_while/H0.
  * apply/impT_conseq_L/Append_assoc_L/Append_monotone_L.
    apply/impT_conseq_L/Sglt_Dup_2/Dup_monotone.
    by exact: andS_comm.
  by apply: (impS_conseq_L _ H); exact: andS_left.
- apply/semax_conseq/IHsemax/v0/Append_monotone_R=>//.
  by apply/(andS_cont H).
- have hpre: (exS u andS v0) ->> exS (fun x => u x andS v0)
    by move => st0 [[x h0] h1]; exists x.
  have hpost: (exT (fun x => [|v0|] *** p x)) =>> ([|v0|] *** exT p).
  * move => tr0 [x h0]. move hp: (p x) => px. rewrite hp in h0.
    destruct px as [q hq]. simpl in h0.
    destruct h0 as [tr1 [[st0 [h0 h2]] h1]].
    inv h2. inv h1=>/=.
    exists (Tnil (hd tr0)). split; first by exact: mk_singleton_nil.
    apply follows_nil => //. exists x. by rewrite hp.
  apply: (semax_conseq hpre hpost). apply: semax_ex => {hpre hpost}x.
  by apply: H0.
Qed.

(* Lemma 3.5 *)
Lemma push_pre: forall u s p, semax u s p -> semax u s ([|u|] *** p).
Proof.
move => u s p hs. by apply/semax_conseq_L/push_pre_andS/hs.
Qed.
