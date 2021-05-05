From CoindSemWhile Require Import SsrExport Trace Language Semax Assert AssertClassical.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition udt (u: assertS) (x: id) (a: expr): assertS :=
fun st => exists st0 : state, (u st0) /\ (update x (a st0) st0 = st).

Inductive hsemax : assertS -> stmt -> assertS -> Prop :=

| hsemax_skip: forall u,   hsemax u Sskip u

| hsemax_assign: forall u x a,
  hsemax u (Sassign x a) (udt u x a)

| hsemax_seq: forall s1 s2 u1 u2 u3,
  hsemax u1 s1 u2->
  hsemax u2 s2 u3 ->
  hsemax u1 (Sseq s1 s2)  u3

| hsemax_ifthenelse: forall a s1 s2 u1 u2,
  hsemax (u1 andS eval_true a) s1 u2 ->
  hsemax (u1 andS eval_false a) s2 u2 ->
  hsemax u1 (Sifthenelse a s1 s2) u2

| hsemax_while:forall a s u,
  hsemax (u andS eval_true a) s u ->
  hsemax u (Swhile a s) (u andS eval_false a)

| hsemax_conseq: forall s u1 u2 v1 v2,
  u1 ->> u2 ->
  v2 ->> v1 ->
  hsemax u2 s v2 ->
  hsemax u1 s v1

| hsemax_ex: forall s (A : Type) (u: A -> assertS) (v: A -> assertS),
  (forall x, hsemax (u x) s (v x)) ->
  hsemax (exS u) s (exS v).

Lemma hsemax_conseq_L: forall s u1 u2 v,
u1 ->> u2 -> hsemax u2 s v -> hsemax u1 s v.
Proof.
move => s u1 u2 v h0 h1.
exact: hsemax_conseq h0 (@assertS_imp_refl v) h1.
Qed.

Lemma hsemax_conseq_R: forall s u v1 v2,
v2 ->> v1 -> hsemax u s v2 -> hsemax u s v1.
Proof.
move => s u v1 v2 h0 h1.
have := hsemax_conseq (@assertS_imp_refl u)  h0 h1.
by apply.
Qed.

Lemma Last_destruct : forall (p: assertT) st tr,
 satisfy p tr -> fin tr st -> Last p st.
Proof.
move => [f h] st tr /= h0 h1. exists tr.
by split.
Qed.

(* Proposition 4.3: projecting the trace-based Hoare logic into
   the partial-correctness Hoare logic. *)
Lemma semax_correct_hsemax: forall u s p,
semax u s p -> forall v, hsemax (v andS u) s (Last ([|v|] *** p)).
Proof.
induction 1.
- move => v. have h0 := hsemax_skip (v andS u).
  have h1 := (@singleton_andS_append u v).
  by apply: (hsemax_conseq_R h1 h0).
- move => v. have h0 := hsemax_assign (v andS u) x a.
  have h1: (udt (v andS u) x a) ->> (Last ([|v|] *** Updt u x a)).
  * move => st0 [st1 [[{}h0 h1] h2]].
    exists (Tcons st1 (Tnil st0)). split.
    + exists (Tnil st1). split.
      - exists st1; split => //. by apply bisim_reflexive.
      apply: follows_nil=>//. rewrite /updt. exists st1. split => //.
      rewrite h2. by apply: bisim_reflexive.
    by apply/fin_delay/fin_nil.
  by apply: (hsemax_conseq_R h1 h0).
- move => v0.
  have h: Last ([|Last ([|v0|] *** p1 *** [|v|])|] *** p2) ->>
  Last ([|v0|] *** p1 *** p2).
  * move => st0 h0. have h1 := Last_Last h0 => {h0}.
    apply: (Last_monotone _ h1) => {h1 st0}.
    have h0 := (@Append_assoc_L ([|v0|]) (p1 *** ([|v|])) p2).
    apply: (impT_conseq_L h0) => {h0}.
    by apply/Append_monotone_R/Append_monotone_L/Append_Singleton.
  apply/(hsemax_conseq_R h)/(hsemax_seq (IHsemax1 _))/(hsemax_conseq_L _ (IHsemax2 _)).
  move => st0 h0. split=>//.
  by apply/(@Last_chop_sglt ([|v0|] *** p1) v)/(Last_monotone _ h0)/Append_assoc_R.
- move => v.
  have hpost : (Last ([|v andS u|] *** p)) ->> (Last ([|v|] *** <<u>> *** p)).
  * destruct p as [p hp]. move => st0 [tr0 [[tr1 [[st1 [h4 h3]] h2]] h1]] /=.
     inv h3. inv h2. move: h4 => [h2 h3]. exists (Tcons (hd tr0) tr0).
     split.
     + exists (Tnil (hd tr0)). split.
       - exists (hd tr0). split => //. by apply bisim_reflexive.
       apply follows_nil =>//.
       exists (Tcons (hd tr0) (Tnil (hd tr0))). split.
       - exists (hd tr0). split => //. by apply bisim_reflexive.
       apply/follows_delay/follows_nil =>//. by apply: fin_delay.
  apply hsemax_ifthenelse.
  * have hpre: ((v andS u) andS eval_true a) ->>
     ((v andS u) andS u andS eval_true a).
      * move => st0 [h0 h1]. split => //. move: h0 => [h0 h2]. by split.
     have h0 := IHsemax1 (v andS u) => {IHsemax1}.
     move: (hsemax_conseq_L hpre h0) => {}h0.
     apply: (hsemax_conseq_R hpost h0).
  * have hpre: ((v andS u) andS eval_false a) ->>
     ((v andS u) andS u andS eval_false a).
      * move => st0 [h0 h1]. split => //. move: h0 => [h0 h2]. by split.
     have h0 := IHsemax2 (v andS u) => {IHsemax1 IHsemax2}.
     move: (hsemax_conseq_L hpre h0) => {}h0.
     apply: (hsemax_conseq_R hpost h0).
- move => w.
  set inv := Last ([|w|] *** <<u0>> *** Iter ( p *** <<u>>)).
  have h0 := IHsemax inv => {IHsemax H0}.
  have h1: (inv andS eval_true a) ->> (inv andS u andS eval_true a).
  * move => st [{}h0 h1]. do!split => //. clear h1.
    destruct p as [f hf]. simpl in inv.
    move: h0 => [tr [[tr0 [[st0 [_ h3]] h2]] h1]].
    inv h3. inv h2. move: H2 => [tr0 [[st0 [h3 h4]] h2]]. inv h4.
    inv H2. inv h2. inv h1. inv H3. have h0 := H _ h3 => {h3}.
    have h1: satisfy (ttT *** [|u|]) tr'.
    * apply iter_last. simpl. exists (Tnil (hd tr')). split.
      exists (hd tr'). split => //. by apply bisim_nil.
      apply follows_nil => //.
      by apply: (iter_cont (@append_cont_L _ _ _ _) H2).
    simpl in h1. clear H2 h0. move: h1 => [tr0 [_ h1]].
    move: tr' st H4 tr0 h1. induction 1.
    - move => tr0 h0. inv h0. move: H1 => [st0 [h0 h1]]. by inv h1.
    - move => tr0 h0. inv h0. move: H1 => [st0 [_ h0]]. inv h0.
      by apply: (IHfin _ H2).
  have h2 := hsemax_conseq_L h1 h0 => {h0 h1}.
  have h0 : Last ([|inv|] *** p *** [|u|]) ->> inv.
  * move => {h2} st0 h0. have h1 := Last_Last h0 => {h0}.
    apply: (Last_monotone (@Append_assoc_L _ _ _)).
    apply: (Last_monotone (@Append_monotone_R _ _ _ (@Iter_unfold_1 _))).
    apply: (Last_monotone (@Append_assoc_L _ _ _)).
    apply: (Last_monotone (@Append_assoc_L _ _ _)).
    have : Last ((((([|w|]) *** (<< u0 >>)) *** Iter (p *** (<< u >>))) *** p) ***
    ([|u|])) st0.
    * apply: (Last_monotone (@Append_assoc_R _ _ _)).
      by apply: (Last_monotone (Append_monotone_L (@Append_assoc_R _ _ _))).
    by apply/Last_dup.
  have h1 := hsemax_conseq_R h0 h2 => {h0 h2}.
  have h0 := hsemax_while h1 => {h1}.
  apply: (hsemax_conseq _ _ h0).
  * move => st0 {}h0. rewrite /inv.
    apply: (Last_monotone
    (@Append_monotone_R _ _ _ (@Append_monotone_R  _ _ _ (@Stop_Iter _)))).
    move: h0 => [h0 h1]. exists (Tcons st0 (Tnil st0)). split.
    + exists (Tnil st0). split.
      - exists st0. split => //. by apply: bisim_reflexive.
      apply: follows_nil=>//. exists (Tcons st0 (Tnil st0)). split.
      - exists st0. split => //. by apply bisim_reflexive.
      apply/follows_delay/follows_nil=>//. exists st0. split => //. by apply bisim_reflexive.
    by apply/fin_delay/fin_nil.
  * rewrite /inv => st0 [h1 h2].
    apply: (Last_monotone (@Append_assoc_L _ _ _)).
    apply: (Last_monotone (@Append_assoc_L _ _ _)).
    apply: (Last_monotone (@Append_monotone_L _ _ _ (@Append_assoc_R _ _ _))).
    destruct p as [p hp]. move: h1 => [tr0 [h1 h3]] /=.
    exists tr0. split => //. exists tr0. split => // {h1}. move: tr0 h3.
    cofix hcoind. move => tr0 h1. inv h1.
    + apply follows_nil=>//. exists st0. split => //. by apply: bisim_reflexive.
    by apply/follows_delay/hcoind.
- move => v. have h := IHsemax v => {IHsemax}.
  have h0 := andS_cont (@assertS_imp_refl _) H.
  apply: (hsemax_conseq_L (h0 _)) => {h0}.
  apply: (hsemax_conseq_R _ h) => {h}.
  by apply/Last_monotone/Append_monotone_R.
- move => v.
  have h0: (v andS exS u) ->> (exS (fun a => v andS u a)).
  * move => st0 [h0 [x h1]]. exists x. by split.
  apply: (hsemax_conseq_L h0) => {h0}.
  have h0: (exS (fun x => Last ([|v|] *** (p x)))) ->> Last ([|v|] *** exT p).
  * move => st0 [x h0]. move hp: (p x) => q. rewrite hp in h0.
    destruct q as [q hq]. simpl in h0. destruct h0 as [tr0 [h0 h1]].
    exists tr0. split => //. clear h1. destruct h0 as [tr1 [h0 h1]].
    exists tr1. split => //. clear h0. move: tr1 tr0 h1. cofix hcoind.
    move => tr0 tr1 h0. inv h0. apply follows_nil => //. exists x.
    rewrite hp. simpl => //. apply follows_delay.
    by apply: hcoind.
  apply: (hsemax_conseq_R h0)=>{h0}.
  by apply: hsemax_ex.
Qed.

(* Corollary 4.2 *)
Lemma semax_correct_hsemax_main: forall u s p,
semax u s p -> hsemax u s (Last p).
Proof.
move => U s P hhsemax.
move: (semax_correct_hsemax hhsemax ttS) => {}hhsemax.
apply: (hsemax_conseq _ _ hhsemax) => {hhsemax}.
 * move => st0 hU. by split.
 * move => st0 h0. destruct P as [P hP]. destruct h0 as [tr0 [h0 h1]].
   exists tr0. split => //. destruct h0 as [h0  [h2 h3]].
   inversion h2; subst; clear h2. destruct H as [_ h2]. clear h1.
   inversion h2; subst; clear h2. inversion h3; by subst.
Qed.

(* Proposition 4.1: embedding the partial-correctness Hoare logic
   into the trace-based Hoare logic *)
Lemma hsemax_correct_semax: forall u s v,
hsemax u s v -> semax u s (ttT *** [|v|]).
Proof.
induction 1.
- have h0 := semax_skip u.
  have h1: ([|u|]) =>> (ttT *** [|u|]).
  * move => tr0 [st0 [h1 h2]]. inv h2. exists (Tnil st0). split => //.
     apply follows_nil =>//. exists st0. split; [done | apply bisim_nil].
  by apply: (semax_conseq_R h1 h0).
- have h0 := semax_assign u x a.
  have h1: (Updt u x a) =>> (ttT *** [|udt u x a|]).
  * move => tr0 [st0 [h1 h2]]. exists tr0. split => //. inv h2. inv H1.
    apply/follows_delay/follows_nil=>//.
    exists (update x (a st0) st0).
    split; last by apply bisim_nil. exists st0. by split.
  by apply: (semax_conseq_R h1 h0).
- have h0 := semax_seq IHhsemax1 IHhsemax2 => {IHhsemax1 IHhsemax2}.
  have h1 := semax_conseq_R (@Append_assoc_R _ _ _) h0 => {h0}.
  apply: (semax_conseq_R (@Append_monotone_L _ _ _ (@ttT_idem_comp)) h1).
- have h0 := semax_ifthenelse IHhsemax1 IHhsemax2 => {IHhsemax1 IHhsemax2 H H0}.
  have h1: (<<u1>> *** ttT *** [|u2|]) =>> (ttT *** [|u2|]).
  * move => tr0 {}h0. move: (append_assoc_R h0) => [tr1 [{}h0 h1]].
    exists tr1. by split.
  by apply: (semax_conseq_R h1 h0).
- have h0: u ->> u by [].
  have h1 := semax_while h0 IHhsemax => {h0 IHhsemax}.
  set p0 := (ttT *** << u >>).
  have h0: ((<< u >>) *** Iter p0 *** [|eval_false a|]) =>>
  (ttT *** [|u andS eval_false a|]).
  * move => tr0 [tr1 [[st0 [h0 h2]] {}h1]].
    inv h2. inv H2. inv h1. inv H3. exists (Tcons (hd tr') tr').
    split=>//. apply follows_delay. move: tr' H2 h0.
    cofix hcoind0. move => tr0 [tr1 [h0 h2]] h1.
    inv h0. inv h2. move: H2 => [st0 [h0 h2]]. inv h2. simpl in h1.
    apply follows_nil => //. exists st0. split => //. by apply: bisim_reflexive.
    clear h1. move: tr tr1 tr0 H0 H1 h2. cofix hcoind1.
    move => tr0 tr1 tr2 [tr3 [h0 h3]] h1 h2. inv h3.
    + clear h0. move: H1 => [st0 [h0 h3]]. inv h3. inv H2. inv h1.
      inv H3. inv h2. rewrite (follows_hd H4) in h0.
      apply: (follows_delay (hd tr')); apply: (hcoind0 _ _ h0).
      exists tr'. split; by [apply H4 | apply H2].
    inv h1. inv h2.
    clear h0 hcoind0. apply follows_delay.
    apply: (hcoind1 _ _ _ _ H4 H5). exists tr. by split=>//; apply H0.
  by apply: (semax_conseq_R h0 h1).
- have h0 := Singleton_monotone H0.
  have h1 := (@Append_monotone_R ttT _ _ h0) => {h0}.
  have h0 := semax_conseq_R h1 IHhsemax => {h1 IHhsemax}.
  apply: (semax_conseq_L H h0).
- have h0: (exT (fun x => ttT *** [|v x|])) =>> (ttT *** [|exS v|]).
  * move => tr0 [x h0]. simpl in h0. simpl. destruct h0 as [tr1 [h0 h1]].
    exists tr1. split => //. clear h0. move: tr1 tr0 h1. cofix hcoind.
    move => tr0 tr1 h0. inv h0.
    + apply follows_nil => //. destruct H2 as [st0 [h0 h1]].
      exists st0; split => //. by exists x.
    by apply/follows_delay/hcoind.
  apply: (semax_conseq_R h0) => {h0}.
  by apply semax_ex.
Qed.
