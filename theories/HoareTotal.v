From CoindSemWhile Require Import SsrExport Trace Language BigFunct.
From CoindSemWhile Require Import Assert AssertClassical Semax SemaxSound.
From Coq Require Import Lia Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* copied from Hoare *)
Definition udt (u: assertS) (x: id) (a: expr): assertS :=
  fun st => exists st0 : state, (u st0) /\ (update x (a st0) st0 = st).

Inductive tsemax2: assertS -> stmt -> assertS -> Prop :=

| tsemax2_skip: forall u, tsemax2 u Sskip u

| tsemax2_assign: forall u x a,
  tsemax2 u (Sassign x a) (udt u x a)

| tsemax2_seq: forall s1 s2 u1 u2 u3,
  tsemax2 u1 s1 u2->
  tsemax2 u2 s2 u3 ->
  tsemax2 u1 (Sseq s1 s2) u3

| tsemax2_ifthenelse: forall a s1 s2 u1 u2,
  tsemax2 (u1 andS eval_true a) s1 u2 ->
  tsemax2 (u1 andS eval_false a) s2 u2 ->
  tsemax2 u1 (Sifthenelse a s1 s2) u2

| tsemax2_while:forall a s m (J: nat -> assertS),
  (forall n, tsemax2 (eval_true a andS (J n)) s
   (exS (fun k => (fun st => k < n) andS (J k))))->
  tsemax2 (J m) (Swhile a s) (exS (fun k => (fun st => k <= m) andS J k andS eval_false a))

| tsemax2_conseq: forall s u1 u2 v1 v2,
  u1 ->> u2 ->
  v2 ->> v1 ->
  tsemax2 u2 s v2 ->
  tsemax2 u1 s v1

| tsemax2_ex: forall s (A: Type) (u: A -> assertS) (v: A -> assertS),
  (forall x, tsemax2 (u x) s (v x)) ->
  tsemax2 (exS u) s (exS v).

Lemma tsemax2_conseq_L: forall s u1 u2 v,
  u1 ->> u2 -> tsemax2 u2 s v -> tsemax2 u1 s v.
Proof.
move => s u1 u2 v h0 h1.
by apply/tsemax2_conseq/h1.
Qed.

Lemma tsemax2_conseq_R: forall s u v1 v2,
v2 ->> v1 -> tsemax2 u s v2 -> tsemax2 u s v1.
Proof.
move => s u v1 v2 h0 h1.
by apply/tsemax2_conseq/h1.
Qed.

Lemma tsemax2_false: forall s u, tsemax2 ffS s u.
Proof.
move => s. induction s=>u.
- by apply/tsemax2_conseq_R/tsemax2_skip.
- by apply/tsemax2_conseq_R/tsemax2_assign=>st0 [st1][h0 _].
- by apply/tsemax2_seq/IHs2.
- by apply/tsemax2_ifthenelse;
    (apply/tsemax2_conseq_L; first by exact: andS_left).
- set J := fun m: nat => ffS.
  apply/tsemax2_conseq/(tsemax2_while 0 (J:=J))=>//.
  - by move=>st0 [n0][h0 [h1 _]].
  move => n.
  apply: (tsemax2_conseq _ _ (IHs (exS (fun k => (fun st => k < n) andS J k))))=>//.
  by rewrite /J => st [_ h].
Qed.

Inductive len: nat -> trace -> Prop :=
| len_stop: forall n st, len n (Tnil st)
| len_delay: forall n st tr, len n tr -> len (S n) (Tcons st tr).

Lemma len_S: forall n tr, len n tr -> len (S n) tr.
Proof.
by induction 1; [apply: len_stop|apply: len_delay].
Qed.

Lemma len_monotone: forall n m, n <= m ->
  forall tr, len n tr -> len m tr.
Proof.
move=> n m h0 tr h1.
rewrite (_: m = (m - n) + n); last by lia.
suff: forall p q tr, len q tr -> len (p + q) tr by apply.
move=> {n m tr h0 h1}p. induction p=>q tr.
+ by rewrite (_: 0 + q = q) //; lia.
+ move=> h0. rewrite (_: S p + q = S (p + q)); last by lia.
  by apply/len_S/IHp.
Qed.

Definition Len (p: assertT) (n: nat) : assertS :=
  fun st => forall tr, (hd tr = st) /\ (satisfy p tr) -> len n tr.

(* Lemma 4.1: ⌈P⌉n is anti-monotone. *)
Lemma Len_monotone: forall n p q, q =>> p -> Len p n ->> Len q n.
Proof.
move => n p q hpq st0. rewrite /Len => hp tr0 [h0 h1].
apply hp. split => //. by apply: hpq.
Qed.

Lemma Len_monotone2: forall p n m, n <= m -> Len p n ->> Len p m.
Proof.
move => p n m hnm st0 h0 tr0 [h1 h2].
by apply/(len_monotone hnm)/h0.
Qed.

Definition after (p: assertT) (q: assertT) :=
  let: exist p hp := p in let: exist q hq := q in
  forall tr, p tr -> exists tr0: trace, follows q tr tr0.

(* Lemma 4.2: ◃ is monotone on the left argument . *)
Lemma after_monotone_L: forall p0 p1 q, p0 =>> p1 ->
  after p1 q -> after p0 q.
Proof.
move => [p0 hp0] [p1 hp1] [q hq] h0 h1 tr1 h2.
move: (h0 _ h2) => /= {}h2.
by apply: h1.
Qed.

Definition invert_fin_delay (tr : trace) (st st0 : state)
 (h : fin (Tcons st tr) st0) : fin tr st0.
Proof. by depelim h. Defined.

Fixpoint cut (tr0 : trace) (st0 : state) (h : fin tr0 st0) (tr1 : trace) { struct h }: trace :=
match tr0 as tr0' return (fin tr0' st0 -> trace) with
| Tnil _ => fun _ => tr1
| Tcons st tr => fun h' =>
  match tr1 with
  | Tnil _ => tr1
  | Tcons st1 tr1' => cut (invert_fin_delay h') tr1'
  end
end h.

Lemma tsemax2_complete_aux: forall (p q : trace -> Prop) tr0 st0 (h:fin tr0 st0),
 forall tr1 tr2, hd tr1 = st0 -> follows q (tr0 +++ tr1) tr2 ->
 p tr1 -> append p q (cut h tr2).
Proof.
move => p q.
refine (fix IH tr st h {struct h} := _).
case: tr st h.
- depelim h => tr0 tr1 h0 h2 h3.
  rewrite trace_append_nil in h2. simpl.
  by exists tr0.
- depelim h => tr0 tr1 h1 h2 h3.
  rewrite trace_append_cons in h2. inv h2=>/=.
  by apply: (IH _ _ _ _ _ _ H2).
Qed.

Lemma tsemax2_complete_aux2: forall p tr0 st0 (h: fin tr0 st0),
 forall tr1 tr2, follows p (tr0 +++ tr1) tr2 ->
 hd (cut h tr2) = hd tr1.
Proof.
move => p.
refine (fix IH tr st h {struct h} := _).
case: tr st h.
- depelim h => tr0 tr1.
  rewrite trace_append_nil /= => h0.
  by apply/esym/(follows_hd h0).
- depelim h => tr0 tr1.
  rewrite trace_append_cons /= => h1. inv h1.
  by apply: (IH  _ _ _ _ _ H2).
Qed.

Lemma tsemax2_complete_aux3: forall u0 w u p st0, u0 ->> u ->
 Last (<< u0 andS w >> *** Iter (p *** << u >>)) st0 -> u st0.
Proof.
move => u0 w u p st0 a0 h2.
have {h2}h4 : Last ((<< u >>) *** Iter (ttT *** (<< u >>))) st0.
* apply/(Last_monotone _ h2)/Append_monotone.
  - move => tr0 [st1 [h4 h5]] /=. inv h5. inv H1. destruct h4 as [h4 h5].
    by apply/mk_dup/a0.
  - by apply/Iter_monotone/Append_monotone_L.
by apply: (Last_chop_sglt (Last_monotone (@iter_last_dup _) h4)).
Qed.

(* Lemma 4.3: (P ** Q) ◃ R ⊧ (<Last P> ** Q) ◃ R *)
Lemma after_Append: forall p q r, after (p *** q) r -> after ([|Last p|] *** q) r.
Proof.
move => [p hp] [q hq] [r hr] /= h0 tr0 [tr1 [[st0 [h1 h3]] h2]].
inv h3. inv h2. destruct h1 as [tr1 [h1 h2]].
have h3: (p *+* q) (tr1 +++ tr0).
* exists tr1; split => // {h1}. move: tr0 tr1 H1 h2.
  cofix CIH=> tr0. case=>st0.
  - move=>h2 h1. inv h1. rewrite trace_append_nil. by apply follows_nil.
  - move=>tr1 h2 h3. inv h3. rewrite [Tcons st0 tr1 +++ _]trace_destr /=.
    by apply/follows_delay/(CIH _ _ h2).
move: (h0 _ h3) => {h0 H1 h1 h3}[tr2 h0].
move h1 : (hd tr0) => st0. rewrite h1 in h2. move: tr1 st0 h2 tr0 h1 tr2 h0.
induction 1=> tr0 h0 tr1 h1.
- rewrite trace_append_nil in h1.
  by exists tr1.
- rewrite trace_append_cons in h1. inv h1.
  by apply: (IHh2 _ _ _ H2).
Qed.

(* Lemma 4.4 *)
Lemma after_Last: forall p r, after ([|Last p|]) r -> after p r.
Proof.
move => [p hp] [q hq] /= h0 tr0 h1.
by apply/fin_hd_follows/singleton_last_fin/h1.
Qed.

(* Proposition 4.4: projecting the total-correctness Hoare logic into
   the trace-based Hoare logic. *)
Lemma tsemax2_complete: forall u s p, semax u s p ->
forall m w r, after ([|w|] *** p) r -> tsemax2 (u andS w andS (Len (p *** r) m)) s
(Last ([|w|] *** p) andS (Len r m)).
Proof.
induction 1.
- move => m w r hafter.
  have h0 := tsemax2_skip (u andS w andS Len (([|u|]) *** r) m).
  apply: (tsemax2_conseq_R _ h0) => st [{}h0 [h1 h2]].
  split.
  * exists (Tnil st). split; last by exact: fin_nil.
    exists (Tnil st). split; first by exact: mk_singleton_nil.
    by apply/follows_nil/mk_singleton_nil.
  move => tr [h3 h4]. apply h2. split => //. destruct r as [r hr]. simpl.
  simpl in h4. exists (Tnil st).
  by split; [exact: mk_singleton_nil| exact: follows_nil].
- move => m w r hafter.
  have h0 := tsemax2_assign (u andS w andS Len (Updt u x a *** r) m) x a.
  apply: (tsemax2_conseq_R _ h0) => st [st1 [[{}h0 [h2 h3]] h1]].
  split.
  * exists (Tcons st1 (Tnil st)). split; last by apply/fin_delay/fin_nil.
    exists (Tnil st1). split; first by exact: mk_singleton_nil.
    rewrite -h1. by apply/follows_nil/mk_updt.
  move => tr0 [h4 h5].
  have {h1 h2 h3 h4 h5}h0: len m (Tcons st1 tr0).
  * apply h3 => {h3}. split => //. destruct r as [r hr]. simpl. exists (Tcons st1 (Tnil st)).
    split; first by rewrite -h1; exact: mk_updt.
    by apply/follows_delay/follows_nil.
  inv h0. by apply: len_S.
- move => m w r hafter.
  have hr: after ([|w|] *** p1 *** [|v|]) (p2 *** r).
  * have h: after ([|w|] *** p1 *** [|v|]) p2.
    * apply: (after_monotone_L (@Append_assoc_R _ _ _)).
      apply after_Last.
      apply: (after_monotone_L (Singleton_monotone (@Last_chop_sglt _ _))).
      destruct p2 as [p2 hp2]. move => /= tr0 [st0 [h0 h1]].
      inv h1. move: (semax_total H0 h0) => [tr0 [{}h0 /= h1]].
      exists tr0. by apply: follows_nil.
    destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2]. destruct r as [r hr].
    simpl. simpl in hafter. simpl in h. move => tr0 h0.
    move: (h _ h0) => {h}[tr1 h1].
    have : (singleton w *+* p1 *+* p2) tr1.
    * apply append_assoc_L. exists tr0. split => //.
      move: (append_assoc_R h0) => {}h0.
      by apply/(append_singleton _ h0)/append_setoid.
    move => h2. move: (hafter _ h2) => {hafter}[tr2 h3].
    exists tr2. apply: (follows_follows h1 h3).
  have hs1 := IHsemax1 m w (p2 *** r) hr => {IHsemax1 hr}.
  have h0: (Len ((p1 *** p2) *** r) m) ->> Len ((p1 *** [|v|]) *** p2 *** r) m.
  * apply Len_monotone. apply: (impT_conseq_L (@Append_monotone_L _ p1 _ _)).
    - by apply: Append_Singleton.
    by apply Append_assoc_R.
  have {h0}hs1 : tsemax2 (u andS w andS Len ((p1 *** p2) *** r) m)
               s1 (Last (([|w|]) *** p1 *** ([|v|])) andS Len (p2 *** r) m).
  * apply: (tsemax2_conseq_L _ hs1) => {hs1} st0 [h1 [h2 h3]].
    split => //. split => //. by exact: (h0 _ h3).
  have hr: after ([|Last ([|w|] *** p1 *** [|v|])|] *** p2) r.
  * destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2]. destruct r as [r hr].
    simpl. simpl in hafter. move => {hs1} tr0 h0. destruct h0 as [tr1 [h0 h1]].
    destruct h0 as [st0 [h0 h2]]. inv h2. inv h1. destruct h0 as [tr1 [h0 h1]].
    have {H3} h0 : (singleton w *+* p1 *+* p2) (tr1 +++ tr0).
    * apply append_assoc_L.
      have {}h0 := append_assoc_R h0.
      apply: (append_fin _ H3) => //.
      apply: (append_singleton _ h0) => //.
      by apply append_setoid.
    have {hafter} [tr2 {}h0] := hafter _ h0.
    move h2: (hd tr0) => st0. rewrite h2 in h1.
    exists (cut h1 tr2). move: tr1 st0 h1 tr0 h2 tr2 h0.
    refine (fix IH tr st h {struct h} := _).
    case: tr st h.
    - depelim h; move => tr0 h0 tr2 h1. rewrite trace_append_nil in h1. simpl. done.
    - depelim h; move => tr0 h2 tr2 h1. simpl. rewrite trace_append_cons in h1. inv h1.
      by apply: (IH  _ _ _ _ _ _ H4).
  have hs2 := IHsemax2 m (Last (([|w|]) *** p1 *** ([|v|]))) r hr => {IHsemax2 hr}.
  have h0: (Last (([|w|]) *** p1 *** ([|v|]))) ->> v.
  * move => st0 h0.
    move: (Last_monotone (@Append_assoc_R _ _ _) h0) => {}h0.
    by exact: (Last_chop_sglt h0).
  have {}hs2: tsemax2 (Last (([|w|]) *** p1 *** ([|v|]))andS Len (p2 *** r) m) s2
  (Last (([|Last (([|w|]) *** p1 *** ([|v|]))|]) *** p2) andS Len r m).
  * apply: (tsemax2_conseq_L _ hs2) => {hs2} st0 [h1 h2].
    split => //.
    by exact: (h0 _ h1).
  move: (tsemax2_seq hs1 hs2) => {h0 hs1 hs2} hs.
  apply: (tsemax2_conseq_R _ hs) => {hs} st0 [h0 h1].
  split => // {h1}. move: (Last_Last h0) => {}h0.
  apply: (Last_monotone _ h0) => {h0}.
  apply: (impT_conseq_R (@Append_assoc_L _ _ _)).
  by apply/Append_monotone_L/Append_monotone_R/Append_Singleton.
- move => m w r hafter.
  * have haftertt: after ([|w andS u|] *** p) r.
    * destruct p as [p hp]. destruct r as [r hr]. simpl. clear IHsemax1 IHsemax2.
      simpl in hafter. move => tr0 [tr1 [h0 h1]]. destruct h0 as [st0 [h0 h2]].
      inv h2. inv h1. destruct h0 as [h0 h1].
      have h2: (singleton w *+* dup u *+* p) (Tcons (hd tr0) tr0).
      * exists (Tnil (hd tr0)). split; first by exact: mk_singleton_nil.
        apply follows_nil => //. exists (Tcons (hd tr0) (Tnil (hd tr0))).
        split; first by exact: mk_dup.
        by apply/follows_delay/follows_nil.
      move: (hafter _ h2) => {h0 h1 h2} [tr1 h3]. inv h3.
      by exists tr'.
    apply tsemax2_ifthenelse.
    - move: (IHsemax1 m _ _ haftertt) => {IHsemax1 haftertt} hsemax.
      apply: (tsemax2_conseq _ _ hsemax) => {hsemax}.
      * move => st0 [[h0 [h1 h3]] h2]. split => //. split => //.
        move: (Len_monotone (@Append_assoc_R _ _ _) h3) => {}h3.
        destruct p as [p hp]. destruct r as [r hr]. move => tr0 [{}h1 /= {}h2].
        have f4 : ((dup u) *+* (p *+* r)) (Tcons (hd tr0) tr0).
        + exists (Tcons (hd tr0) (Tnil (hd tr0))). split; first by rewrite h1; exact: mk_dup.
          by apply/follows_delay/follows_nil.
        have h5: len m (Tcons (hd tr0) tr0) by apply: h3.
        inv h5. by exact: len_S H3.
       * move => st0 [h0 h1]. split => // {h1}. destruct p as [p hp].
         destruct h0 as [tr0 [h0 h1]]. exists (Tcons (hd tr0) tr0).
         destruct h0 as [tr1 [h0 h2]]. destruct h0 as [st1 [h0 h3]].
         inv h3. inv h2. destruct h0 as [h0 h2]. split; last by exact: fin_delay.
         exists (Tnil (hd tr0)). split; first by exact: mk_singleton_nil.
         apply follows_nil => //.
         exists (Tcons (hd tr0) (Tnil (hd tr0))). split; first by exact: mk_dup.
         by apply/follows_delay/follows_nil.
    move: (IHsemax2 m _ _ haftertt) => {IHsemax2 haftertt} hsemax.
    apply: (tsemax2_conseq _ _ hsemax) => {hsemax}.
    * move => st0 [[h0 [h1 h3]] h2]. split => //. split => //.
      move: (Len_monotone (@Append_assoc_R _ _ _) h3) => {}h3.
      destruct p as [p hp]. destruct r as [r hr]. move => tr0 [{}h1 /= {}h2].
      have h4 : ((dup u) *+* (p *+* r)) (Tcons (hd tr0) tr0).
      + exists (Tcons (hd tr0) (Tnil (hd tr0))). split; first by rewrite h1; exact: mk_dup.
        by apply/follows_delay/follows_nil.
      have h5: len m (Tcons (hd tr0) tr0) by apply: h3.
      inv h5. by exact: len_S H3.
     * move => st0 [h0 h1]. split => //. clear h1. destruct p as [p hp].
       destruct h0 as [tr0 [h0 h1]]. exists (Tcons (hd tr0) tr0).
       destruct h0 as [tr1 [h0 h2]]. destruct h0 as [st1 [h0 h3]].
       inv h3. inv h2. destruct h0 as [h0 h2]. split; last by exact: fin_delay.
       exists (Tnil (hd tr0)). split; first by exact: mk_singleton_nil.
       apply follows_nil => //.
       exists (Tcons (hd tr0) (Tnil (hd tr0))). split; first by exact: mk_dup.
       by apply/follows_delay/follows_nil.
- move => m w r hafter.
  set J0 := Last (<< u0 andS w >> *** (Iter (p *** << u >>))).
  set J1 := (Iter (p *** << u >>) *** [|eval_false a|] *** r).
  set Q := <<u>> *** (Iter (p *** <<u>>)) *** [|eval_false a|] *** r.

  have hs: forall n, tsemax2 (eval_true a andS J0 andS Len J1 n) s
  (exS (fun k => (fun st => k < n) andS J0 andS Len J1 k)).

  have hn0: (eval_true a andS J0 andS Len J1 0) ->> ffS.
  * move => st0. rewrite /J0 /J1. move => [h1 [h2 h3]].
    have hfalse: forall tr0, satisfy (Iter (p *** <<u>>) *** [|eval_false a|] *** r) tr0
      -> hd tr0 = st0 -> False.
    * destruct p as [p hp]. destruct r as [r hr]. simpl. move => tr0 h4 h5.
       have {}h3 : len 0 tr0 by apply h3.
       destruct h4 as [tr1 [h4 h6]]. inv h4.
       - inv h6. destruct H3 as [tr1 [h0 h4]]. destruct h0 as [st1 [h0 h5]].
         inv h5. inv h4. rewrite /eval_true in h1. rewrite /eval_false in h0.
         rewrite h1 in h0. by inv h0.
       - destruct H1 as [tr2 [h0 h4]]. destruct tr2.
         - clear h0. inv h4. destruct H4 as [st0 [_ h0]]. inv h0. inv H4.
           inv H2. inv h6. by inv h3.
         - inv h4. inv H2. inv h6. by inv h3.

    have hsemax := semax_while (@assertS_imp_refl _) H0 => {H0}.
    have h0 := semax_total hsemax => {hsemax}.
    have hu : u st0 by exact: (tsemax2_complete_aux3 H h2).
    move: (h0 _ hu) => [tr0 [{}h0 h4]].

    have {}hafter: after ([|w|] *** <<u0>> *** Iter (p *** <<u>>) *** Iter (p *** <<u>>)
                   *** [|eval_false a|]) r.
     * apply: (after_monotone_L _ hafter) => {hafter}.
       apply/Append_monotone_R/Append_monotone_R.
       apply: (impT_conseq_L (@Append_assoc_R _ _ _)).
       by apply/Append_monotone_L/Iter_Iter.

    set P := ([|w|] *** << u0 >> *** Iter (p *** <<u>>) *** Iter (p *** <<u>>) *** [|eval_false a|]).
    destruct p as [p hp]. destruct r as [r hr]. simpl in h4. simpl in h2.
    destruct h2 as [tr1 [[tr2 [[st1 [h2 h7]] h6]] h5]].
    inv h7. inv H2. destruct h2 as [h2 h0].
    inv h6. inv h5. inv H3. destruct h4 as [tr1 [[st0 [h4 h6]] h5]].
    inv h6. inv H3. inv h5. simpl in H4. simpl in h0. simpl in h2.
    simpl. simpl in h1. inv H5.
    have h5 : append (iter (append p (dup u)))
             (append (iter (append p (dup u))) (singleton (eval_false a))) (tr' +++ tr'0).
    * exists tr'. split => // {hu hfalse H2 h2 h0 h4 h1 h3}. move: tr' tr'0 H4 H3.
      cofix CIH=> tr0 tr1 h0. inv h0=>h0.
      - apply follows_nil => //. by rewrite trace_append_nil.
      rewrite [Tcons st tr +++ tr1]trace_destr/=.
      by apply/follows_delay/CIH/h0.
    have hP : satisfy P (Tcons (hd tr') (tr' +++ tr'0)).
    * rewrite /P /=. exists (Tnil (hd tr')). split; first by exact: mk_singleton_nil.
      apply follows_nil => //.
      exists (Tcons (hd tr') (Tnil (hd tr'))). split; first by exact: mk_dup.
      apply/follows_delay/follows_nil => //. by apply: (hd_append H4 (refl_equal _)).
    simpl in hfalse. rewrite -trace_append_cons in hP.
    have hfinite: fin (Tcons (hd tr') tr') (hd tr'0) by apply fin_delay.
    clear H4 h3.
    move: (hafter _ hP) => {hP hafter} [tr0 h3].
    move heq: (Tcons (hd tr') tr') => tr1.
    rewrite heq in h3 hfinite.
    have h6 := tsemax2_complete_aux hfinite (refl_equal _) h3 H3 => {H3}.
    have {}h6 := append_assoc_L h6.
    have {heq}h6 := hfalse _ h6.
    have h7 := tsemax2_complete_aux2 hfinite h3.
    by move: (h6 h7).

  (* end of hn0 *)

  have hpre: forall n, (eval_true a andS J0 andS Len J1 n) ->>
    (eval_true a andS u andS J0 andS Len (p *** [|u|] *** Q) n).
  * move => n st0 [h0 [h1 h2]]. split => //. split => //.
    + rewrite /J0 in h1.
      have h3:((<< u0 andS w >>) *** Iter (p *** (<< u >>)))
                =>> <<u>> *** Iter (ttT *** <<u>>).
      - apply Append_monotone.
        + apply: Dup_monotone => st1 [h3 h4]. by exact: (H _ h3).
        by apply/Iter_monotone/Append_monotone_L.
      have {}h3 := impT_conseq_L h3 (@iter_last_dup _).
      have {}h3 := Last_monotone h3.
      move: (h3 _ h1) => {h3 h1}.
      by apply: Last_chop_sglt.
    split => //. rewrite /J1 in h2. rewrite /Q.
    apply: (Len_monotone _ h2).
    apply: (impT_conseq_L (@Append_assoc_R _ _ _)).
    apply: (impT_conseq_L (@Append_assoc_R _ _ _)).
    apply: (impT_conseq_L (Append_monotone_L (@Append_assoc_L _ _ _))).
    have h3: ([|u|] *** <<u>>) =>> <<u>>.
    * move => st1 /= [tr0 [[st2 [h3 h5]] h4]]. inv h5.
      by inv h4.
    apply: (impT_conseq_L (Append_monotone_L (Append_monotone_R h3))).
    apply: (impT_conseq_L (@Append_assoc_R _ _ _)).
    by apply/Append_monotone_L/Iter_fold_L.

  (* end of hpre *)

  have hpost: forall n, n > 0 -> (Last ([|J0|] *** p *** [|u|]) andS Len Q n) ->>
  (exS (fun k => (fun st => k < n) andS J0 andS Len J1 k)).
  * move => {hn0 hpre} n hn st0 h0. rewrite /J0 in h0.
    have {}h0 : (Last (<<u0 andS w>> *** Iter (p *** <<u>>)) andS Len Q n) st0.
    - move: h0 => [h0 h1]. split => // {h1}.
      have {}h0 := Last_Last h0.
      have {}h0 := Last_monotone (@Append_assoc_R _ _ _) h0.
      have {}h0 := Last_dup h0.
      have {}h0 := Last_monotone (@Append_assoc_L _ _ _) h0.
      move: (Last_monotone (@Append_assoc_L _ _ _) h0) => {h0}.
      by apply/Last_monotone/Append_monotone_R/Iter_unfold_1.
    rewrite /Q in h0.
    have {}h0 : (Last (<< u0 andS w >> *** Iter (p *** << u >>))
      andS Len (Iter (p *** << u >>) *** [|eval_false a|] *** r)
    (n-1)) st0.
    * destruct h0 as [h0 h1]. split => //. destruct p as [p hp].
      destruct r as [r hr]. move => tr0 [h2 h3]. simpl in h3.
      have h4 : len n (Tcons (hd tr0) tr0).
      + apply: h1=>/=. split => //.
        have hu := tsemax2_complete_aux3 H h0.
        exists (Tcons (hd tr0) (Tnil (hd tr0))). split; first by rewrite h2; exact: mk_dup.
        by apply/follows_delay/follows_nil.
      inv h4. by rewrite (_: S n0 - 1 = n0); last by lia.
    fold J0 in h0. fold J1 in h0. exists (n-1). destruct h0 as [h0 h1].
    by split => //; lia.

   (* end of hpost *)

  case.
  * apply: (tsemax2_conseq_L hn0) => {hn0}. by apply: tsemax2_false.
  * move => n.
    have hn : (S n) > 0 by lia.
    apply: (tsemax2_conseq (hpre _) (hpost _ hn)) => {hpre hpost hn hn0}.
    have hpre : (eval_true a andS u andS J0 andS Len (p *** [|u|] *** Q) (S n))
    ->> (eval_true a andS u andS J0 andS (Len ([|J0|] *** p *** [|u|] *** Q) (S n))).
    * move => st0 [h0 [h1 [h2 h3]]]. split => //. split => //. split => //.
      move => tr0 [h4 h5]. apply h3. split => //.
      by apply/Singleton_Append/h5.
    apply: (tsemax2_conseq_L hpre) => {hpre}.
    apply: (tsemax2_conseq _ _ (IHsemax (S n) J0 Q _)) => {IHsemax} //.
    * move => st0 [h0 [h1 [h2 h3]]]. split => //. split => // tr0 [h4 h5].
      apply h3. split => //.
      move: (@Append_assoc_L _ _ _ _ h5) => {}h5.
      destruct p as [p hp]. destruct r as [r hr]. simpl. simpl in h5.
      exists (Tnil (hd tr0)). split; first by rewrite h4; apply: mk_singleton_nil.
      by apply: follows_nil.

(* prove after ([J0] *** p *** [u]) Q *)
    rewrite /J0. apply after_Append.
    move: (after_monotone_L (@Append_assoc_L _ _ _) hafter) => {}hafter.
    have h0: <<u0 andS w>> =>> [|w|] *** <<u0>>.
    * move => tr0 /= [st0 [h0 h1]]. inv h1. inv H3. destruct h0 as [h0 h1].
      exists (Tnil st0). split; first by exact: mk_singleton_nil.
      by apply/follows_nil/mk_dup.
    move: (after_monotone_L (Append_monotone_L h0) hafter) => {h0}hafter.

    have h0: after (<< u0 andS w >> *** Iter (p *** << u >>) *** p *** [|u|])
    (<< u >> *** Iter (p *** << u >>) *** [|eval_false a|]).
    * apply: (after_monotone_L (@Append_assoc_R _ _ _)).
      apply: (after_monotone_L (@Append_assoc_R _ _ _)).
      apply after_Last.
      apply: (after_monotone_L (Singleton_monotone (@Last_chop_sglt _ _))) => {hafter}.
      have hsemax := semax_while (@assertS_imp_refl _) H0 => {H0}.
      have h0 := semax_total hsemax => {hsemax}.
      destruct p as [p hp]. move => /= tr0 [st0 [h1 h2]]. inv h2.
      move: (h0 _ h1) => [tr0 [{}h0 /= {}h1]].
      exists tr0. apply follows_nil => //.

  (** end of h0 **)

   destruct p as [p hp]. rewrite /Q. destruct r as [r hr].
   simpl. simpl in hafter. simpl in h0. move => tr0 h1.
   move: (append_assoc_L h1) => {}h1.
   move: (h0 _ h1) => [tr1 {}h0].
   have h3 : ((dup (u0 andS w) *+* iter (p *+* dup u) *+* p *+* singleton u)
     *+* (dup u *+* iter (p *+* dup u) *+* singleton (eval_false a))) tr1.
     by exists tr0.
   have: (dup (u0 andS w) *+* iter (p *+* dup u) *+* singleton (eval_false a)) tr1.
   * move: (append_assoc_L h3) => {}h0.
     apply: (append_monotone_R _ h0) => tr2 {}h0.
     move: (append_assoc_R h0) => {}h0.
     move: (append_assoc_R h0) => {}h0.
     apply: (append_cont_L _ h0) => {}tr2 {}h0.
     move: (append_assoc_L h0) => {}h0.
     move: (append_assoc_L h0) => {}h0.
     have {}h1 : forall tr, ((p *+* singleton u) *+* dup u *+* iter (p *+* dup u)) tr ->
     iter (p *+* dup u) tr.
     * move => {h1}tr0 {}h0.
       move: (append_assoc_R h0) => [tr3 [{}h0 h1]].
       apply: (iter_loop _ h1) => {h1}.
       apply: (append_cont_L _ h0).
       by apply: append_singleton.
     move: (append_monotone_R h1 h0) => {h1}h0.
     by exact: iter_iter h0.
   move => {h3}h1.
   move: (hafter _ h1) => [tr2 {}h1].
   exists tr2.
   apply: (follows_monotone (@append_assoc_L _ _ _)).
   apply: (follows_monotone (@append_assoc_L _ _ _)).
   move: (follows_follows h0 h1) => {h1 tr1}h0.
   by apply: (follows_monotone (append_cont_L (@append_assoc_R _ _ _)) h0).

  move: (@tsemax2_while _ _ m _ hs) => {}hs.
  have hpre: (u0 andS w andS Len ((<<u0>> *** Iter (p *** <<u>>) ***
    [| eval_false a|]) *** r) m) ->> J0 andS Len J1 m.
  * have h0: (u0 andS w) ->> J0.
    * move => st0 [h0 h1]. rewrite /J0. destruct p as [p hp]. simpl.
      exists (Tcons st0 (Tnil st0)). split; last by apply/fin_delay/fin_nil.
      exists (Tcons st0 (Tnil st0)). split; first by apply: mk_dup.
      by apply/follows_delay/follows_nil/iter_stop.
    have h1: (u0 andS Len ((<<u0>> *** Iter (p *** <<u>>) *** [|eval_false a|]) *** r) m) ->>
      Len J1 m.
    * destruct p as [p hp]. destruct r as [r hr]. move => st0 [h1 h2].
      rewrite /J1. move => tr0 [h4 h3]. simpl in h3.
      have h5: len m (Tcons (hd tr0) tr0).
      * apply h2=>/=. split => //. destruct h3 as [tr1 [h3 h5]].
        have h6 := follows_hd h5. exists (Tcons (hd tr1) tr1). split.
        - exists (Tcons (hd tr1) (Tnil (hd tr1))). split; first by rewrite h6 h4; exact: mk_dup.
          apply/follows_delay/follows_nil => //.
          exists tr1. split => //. clear h0 h1 h2 h4 h3 h6.
          move: tr1 tr0 h5. cofix CIH=> tr0 tr1 h0. inv h0.
          - destruct H2 as [tr0 [h0 h1]]. destruct h0 as [st1 [h0 h2]]. inv h2. inv h1.
            by apply/follows_nil/mk_singleton_nil.
          by apply/follows_delay/CIH/H1.
        rewrite h6. apply follows_delay. clear h0 h1 h2 h3 h4 h6.
        move: tr1 tr0 h5. cofix CIH=>tr0 tr1 h0. inv h0.
        - destruct H2 as [tr0 [h0 h1]]. destruct h0 as [st1 [h0 h2]]. inv h2. inv h1.
          by exact: follows_nil.
        by apply/follows_delay/CIH/H1.
      inv h5. by exact: len_S H3.
    move => st0 [h2 [h3 h4]]. by split; [apply: h0|apply: h1].
  apply: (tsemax2_conseq_L hpre) => {hpre}.
  have hpost : (exS (fun k => (fun _ => k <= m) andS
    (J0 andS Len J1 k) andS eval_false a)) ->> J0 andS Len J1 m andS eval_false a.
  * move => st0 [x [h0 [[h1 h2] h3]]].
    split => //. split => //.
    by apply: (Len_monotone2 h0 h2).
  move: (tsemax2_conseq_R hpost hs) => {hpost}hs.
  have hpost: (J0 andS Len J1 m andS eval_false a) ->>
    Last ([|w|] *** <<u0>> *** Iter (p *** <<u>>) *** [|eval_false a|])
    andS Len r m.
  * move => st0. rewrite /J0 /J1. move => [h0 [h1 h2]]. split.
    - have h3 : (Last (<< u0 andS w >> *** Iter (p *** << u >>)) andS eval_false a) st0
        by split.
      apply/Last_monotone/(Last_andS h3) => {h3}.
      apply: (impT_conseq_L (@Append_assoc_L _ _ _)).
      apply: (impT_conseq_L _ (@Append_assoc_L _ _ _)).
      apply: Append_monotone_L => {h2} tr0 [st1 [{}h0 {}h1]].
      inv h1. inv H3. destruct h0 as [h0 h1]. simpl.
      exists (Tnil st1). split; first by exact: mk_singleton_nil.
      by apply/follows_nil/mk_dup.
    move => tr0 [{}h0 h3]. apply h1. split => //. rewrite -h0 in h2. clear h1 h0.
    destruct r as [r hr]. destruct p as [p hp]. simpl. simpl in h3.
    exists (Tnil (hd tr0)). split; first by exact: iter_stop.
    apply follows_nil => //. exists (Tnil (hd tr0)). split; first by exact: mk_singleton_nil.
    by exact: follows_nil.
  by apply: (tsemax2_conseq_R hpost hs).

- move => m w r hafter.
  have h: after ([|w|] *** p2) r
    by apply/(after_monotone_L _ hafter)/Append_monotone.
  move: (IHsemax m _ _ h) => {hafter h IHsemax}htsemax.
  apply: (tsemax2_conseq _ _ htsemax) => {htsemax}.
  * move => st0 [h0 [h1 h2]]. split; first by apply: H.
    split => //. by apply/Len_monotone/h2/Append_monotone_L.
  move => st0 [h0 h1]. split => //.
  by apply/Last_monotone/h0/Append_monotone_R.

- move => m w r hafter.
  have hsemax: forall x, tsemax2 (u x andS w andS Len (p x *** r) m) s
      (Last (([|w|]) *** p x) andS Len r m).
  * move => x. apply H0. move hp: (p x) => q.
    destruct q as [q hq]. destruct r as [r hr]. move => tr0 [tr1 [h0 h1]].
    have h2 : satisfy ([|w|] *** exT p) tr0.
    - simpl. exists tr1. split => // {h0}.
      move: tr1 tr0 h1. cofix CIH=>tr0 tr1 h0. inv h0.
      - apply follows_nil => //. exists x. by rewrite hp.
      by apply/follows_delay/CIH/H1.
    by exact: hafter _ h2.
  move: (tsemax2_ex hsemax) => {hafter}hsemax.
  apply: (tsemax2_conseq _ _ hsemax) => {hsemax}.
  * move => st0 [[x h0] [h1 h2]]. exists x.
    split => //. split => // tr0 [h3 h4]. apply h2. split => //.
    apply: (Append_monotone_L _ h4) => tr1. move hp: (p x) => [q hq] /= h5.
    exists x. by rewrite hp.
  * move => st0 [x [h0 h1]]. split => // {h1}. move hp: (p x) => q.
    rewrite hp in h0. destruct q as [q hq]. destruct h0 as [tr0 [h1 h0]].
    simpl. exists tr0. split => // {h0}. destruct h1 as [tr1 [h0 h1]].
    exists tr1. split => //. destruct h0 as [st1 [h0 h2]]. inv h2. inv h1.
    apply follows_nil => //. exists x. by rewrite hp.
Qed.

(* Corollary 4.3 *)
Lemma tsemax2_complete_main: forall u s p, semax u s p ->
 tsemax2 (u andS (exS (fun m => Len p m))) s (Last p).
Proof.
move => U s P hsemax.
have h0: (U andS exS (fun m => Len P m)) ->> (exS (fun m => U andS Len P m)).
- move => st0 [h0 [n h1]]. exists n. by split.
have h1: (exS (fun (m:nat) => Last P)) ->> (Last P).
- by move => st0 [n hP].
apply: (tsemax2_conseq h0 h1) => {h0 h1}.
apply tsemax2_ex => n.
move: (@tsemax2_complete _ _ _ hsemax  n ttS ([| ttS |])) => {}hsemax.
have h0 : after (([|ttS|]) *** P) ([|ttS|]).
- clear hsemax. destruct P as [P hP]. move => tr0 h0. exists tr0. by apply follows_ttS.
move: (hsemax h0) => {h0}hsemax.
apply: (tsemax2_conseq _ _ hsemax) => {hsemax}.
- move => st0 h0. destruct h0 as [h0 h1]. do!split=>//.
  move => tr0 [{}h0 h2].
  apply: (h1 tr0) => {h1}; split => //.
  destruct P as [P hP]. simpl in h2. simpl.
  by apply: (append_singleton _ h2).
- destruct P as [P hP]. move => /= st0 [h0 _].
  apply: (last_cont _ h0) => tr0 [tr1 [[st1 [_ h1]] h2]].
  inv h1. by inv h2.
Qed.

Inductive tsemax : assertS -> stmt -> assertS -> Prop :=

| tsemax_skip: forall u, tsemax u Sskip u

| tsemax_assign: forall u x a,
  tsemax u (Sassign x a) (udt u x a)

| tsemax_seq: forall s1 s2 u1 u2 u3,
  tsemax u1 s1 u2->
  tsemax u2 s2 u3 ->
  tsemax u1 (Sseq s1 s2)  u3

| tsemax_ifthenelse: forall a s1 s2 u1 u2,
  tsemax (u1 andS eval_true a) s1 u2 ->
  tsemax (u1 andS eval_false a) s2 u2 ->
  tsemax u1 (Sifthenelse a s1 s2) u2

| tsemax_while:forall a s u (t: state -> nat),
  (forall n, tsemax (eval_true a andS u andS (fun st => t st = n)) s
   (u andS (fun st => t st < n))) ->
  tsemax u (Swhile a s) (u andS eval_false a)

| tsemax_conseq: forall s u1 u2 v1 v2,
  u1 ->> u2 ->
  v2 ->> v1 ->
  tsemax u2 s v2 ->
  tsemax u1 s v1.

Lemma tsemax_conseq_L: forall s u1 u2 v,
 u1 ->> u2 -> tsemax u2 s v -> tsemax u1 s v.
Proof.
move => s u1 u2 v h0 h1.
by apply/tsemax_conseq/h1.
Qed.

Lemma tsemax_conseq_R: forall s u v1 v2,
 v2 ->> v1 -> tsemax u s v2 -> tsemax u s v1.
Proof.
move => s u v1 v2 h0 h1.
by exact/tsemax_conseq/h1.
Qed.

(* Proposition 4.2: embedding the total-correctness Hoare logic into
   the trace-based Hoare logic. *)
Lemma tsemax_correct_semax: forall u s v, tsemax u s v ->
 forall u0, semax (u andS u0) s ([|u0|] *** Finite *** [|v|]).
Proof.
induction 1.
- move => u0.
  apply/semax_conseq_R/(semax_skip (u andS u0)).
  move => tr0 [st0 [[{}h0 h2] h1]]. inv h1.
  exists (Tnil st0). split; first by exact: mk_singleton_nil.
  apply follows_nil => //. exists (Tnil st0). split; first by exact: finite_nil.
  by apply/follows_nil/mk_singleton_nil.
- move => u0.
  apply/semax_conseq_R/(semax_assign (u andS u0)).
  move => tr0 [st0 [[{}h0 h2] h1]]. inv h1. inv H1.
  exists (Tnil st0). split; first by exact: mk_singleton_nil.
  apply follows_nil => //. exists (Tcons st0 (Tnil (update x (a st0) st0))).
  split; first by apply/finite_delay/finite_nil.
  apply/follows_delay/follows_nil=>//. exists (update x (a st0) st0).
  split; last by apply: bisim_nil. exists st0. by split.
- move => u0.
  have h0 := semax_conseq_R (@Append_assoc_R _ _ _) (IHtsemax1 u0) => {IHtsemax1}.
  have h: u2 ->> (u2 andS u2) by [].
  have h1 := semax_seq h0 (semax_conseq_L h (IHtsemax2 u2)) => {h h0 IHtsemax2}.
  have h0: ((([|u0|]) *** Finite) *** ([|u2|]) *** Finite *** ([|u3|]))
  =>> (([|u0|]) *** Finite *** ([|u3|])).
  * move => {h1} tr0 h0.
    have h1 := Append_assoc_L h0 => {h0}.
    apply: (Append_monotone_R _ h1) => {h1}tr0 h0.
    have h1 := Append_assoc_R h0 => {h0}.
    have h0 := Append_assoc_R h1 => {h1}.
    apply: (Append_monotone_L _ h0) => {h0}.
    apply: (impT_conseq_L (Append_monotone_L (@Finite_singleton u2))).
    by apply: Finite_idem_1.
  by apply: (semax_conseq_R h0 h1).
- move => u0.
  have h: ((u1 andS u0) andS eval_true a) ->> (u1 andS eval_true a) andS u0
    by move => st0 [[h0 h1] h2]; do!split.
  have h0: ((u1 andS u0) andS eval_false a) ->> (u1 andS eval_false a) andS u0
    by move => st0 [[h0 h1] h2]; do!split.
  apply: (semax_conseq _ _
            (semax_ifthenelse (semax_conseq_L h (IHtsemax1 u0))
            (semax_conseq_L h0 (IHtsemax2 u0)))) => {h h0 IHtsemax1 IHtsemax2}=>//.
  move => tr0 [tr1 [[st0 [h0 h2]] h1]]. inv h2.
  inv H3. inv h1. exists (Tnil st0). split; first by move: h0=>[_ h0]; apply: mk_singleton_nil.
  inv H4. clear h0.
  move: H3 => [tr0 [[st0 [h0 h2]] h1]]. inv h2. inv h1.
  clear h0. apply follows_nil => //. move: H3 => [tr0 [h0 h1]].
  exists (Tcons (hd tr') tr'). split.
  * have h2 := follows_singleton h1.
    have h3 := finite_setoid h0 h2 => {h0 h2}.
    by apply: finite_delay _ h3.
  have h2 := follows_singleton h1.
  have h3 := follows_setoid_L h1 h2 => {h1 h2}.
  by apply: (follows_delay _ h3).
- move => {H}u0.
  have h: forall n,
            semax ((eval_true a andS u andS (fun st : state => t st = n))
                   andS (fun st => t st = n ))
                  s
                  (([|fun st => t st = n |]) ***
                    Finite ***
                    ([|u andS (fun st : state => t st < n)|]))
    by move => n; apply: H0.
  have h0 := semax_ex h => {H0 h}.
  have h1 : (u andS eval_true a) ->> (exS (fun n : nat =>
    (eval_true a andS u andS (fun st : state => t st = n)) andS (fun st => t st = n))).
  * move => st0 [{}h0 h1]. exists (t st0). by split.
  have h2 := semax_conseq_L h1 h0 => {h1 h0}.
  have h0:(exT (fun n : nat =>
           ([| fun st : state => t st = n |]) ***
           Finite *** ([|u andS (fun st : state => t st < n)|]))) =>>
  ((exT (fun n: nat =>
   [| (fun st: state => t st = n) |] *** Finite ***
   [| (fun st: state => t st < n) |])) *** [|u|]).
  * move => {h2} tr0 [x [tr1 [[st0 [h2 h0]] h1]]].
    inv h0. inv h1. move: H1 => [tr1 [h0 h1]].
    have h3 := follows_singleton h1.
    have h4 := finite_setoid h0 h3 => {h0}.
    have h0 := follows_setoid_L h1 h3 => {h3 h1}.
    exists tr0.
    have h5 := follows_singleton_andS_R h0.
    have h6 := follows_singleton_andS_L h0 => {h0}.
    split=>//. exists (t (hd tr0)). exists (Tnil (hd tr0)). split; first by exact: mk_singleton_nil.
    apply follows_nil => //. by exists tr0.
  have h1 := semax_conseq_R h0 h2 => {h0 h2}.
  have h: (u andS u0) ->> u.  move => st [h0 h2]; done.
  have h0 := semax_while h h1 => { h h1}.
  have h1: ((<< u andS u0 >>) ***
        Iter
          (exT
             (fun n : nat =>
              ([|fun st : state => t st = n|]) ***
              Finite *** ([|fun st : state => t st < n|])) *** (<< u >>)) ***
        ([|eval_false a|])) =>>
  (([|u0 |]) *** Finite *** ([|u andS eval_false a|])).
  * move => tr0 [tr1 [[st0 [[{}h0 h] h2]] h1]].
    inv h2. inv H1. inv h1. inv H2.
    exists (Tnil (hd tr')). split; first by exact: mk_singleton_nil.
    apply follows_nil => //.
    move: H1 => [tr0 [h1 h2]]. exists (Tcons (hd tr') tr'). split; first last.
    - apply/follows_delay/singleton_andS_follows; first last.
      - have h3 := follows_singleton h2.
        by apply: (follows_setoid (@singleton_setoid _) h2 h3 (bisim_reflexive _)).
      have h4 := follows_singleton h2.
      apply: (follows_setoid (@singleton_setoid  _) _ h4 h4) => {h4}.
      have h3 := follows_hd h2 => {h2}. rewrite -h3 in h0 => {h3}.
      by apply: (iter_append_dup h0 h1).
    apply finite_delay.
    have {}h0 := follows_singleton h2 => {h2}.
    apply: (finite_setoid _ h0) => {h0}.
    inv h1; first by exact: finite_nil.
    move: H => [tr1 [[n [tr2 [[st0 [h0 h3]] h2]]] h1]]. inv h3. inv h2.
    move h0: (t (hd tr1)) => n. rewrite h0 in H2. clear h0 h tr'.
    have h: forall (m: nat) (n : nat) (tr1 tr tr0 : trace),
      n <= m ->
      append (fun tr2 : trace => finite tr2)
      (singleton (fun st : state => t st < n)) tr1 ->
      follows (dup u) tr1 tr ->
      follows
      (iter
       (append
          (fun tr2 : trace =>
           exists x : nat,
           satisfy
             (([|fun st : state => t st = x|]) ***
              Finite *** ([|fun st : state => t st < x|])) tr2) (dup u))) tr
      tr0 -> finite tr0.
    * move => {tr0 tr H0 tr1 h1 n H2}m. induction m.
      - move => n tr0 tr1 tr2 h h1 h2 h3.
        have h4: n = 0 by lia.
        rewrite h4 in h1 => {h4 h}.
        move: h1 => [tr3 [h1 h4]].
        move: tr3 h1 tr0 tr1 tr2 h2 h3 h4. induction 1.
        - move => tr0 tr1 tr2 h0 h1 h2. inv h2. move: H1 => [st0 [h3 h4]].
          by inversion h3.
        - move => tr0 tr1 tr2 h0 h2 h3. inv h3. inv h0.
          inv h2.
          by apply/finite_delay/IHh1/H2/H4.
      - move => n tr0 tr1 tr2 h [tr3 [h0 h3]] h1 h2.
        move: tr3 h0 tr0 tr1 tr2 h3 h1 h2. induction 1.
        - move => tr0 tr1 tr2 h0 h1 h2. inv h0. move: H1 => [st0 [h0 h3]].
          inv h3. inv h1. move: H1 => [st0 [h1 h3]]. inv h3. inv H1. simpl in h0.
          inv h2. inv H2. apply finite_delay. inv H1. apply finite_nil.
          move: H => [tr0 [[n0 [tr1 [[st0 [h2 h5]] h4]]] h3]]. inv h5. inv h4.
          rewrite -(follows_hd H0) -(follows_hd h3) in h0.
          have h2: t (hd tr0) <= m by lia. clear h0.
          by apply: (IHm _ _ _ _ h2 H2 h3 H0).
        - move => {IHm} tr0 tr1 tr2 h3 h1 h2. inv h3. inv h1. inv h2.
          by apply/finite_delay/IHh0/H4/H3.
      by apply: (h n _ _ _ _ _ H2 h1 H0).
  by apply: (semax_conseq_R h1 h0).
- move => {H1}u0.
  have h0 := IHtsemax u0 => {IHtsemax}.
  apply: (semax_conseq _ _ h0).
  * move => st0 [{}h0 h1]. by split=>//; apply: H.
  move => tr0 [tr1 [[st0 [{}h0 h2]] h1]].
  inv h2. inv h1. exists (Tnil (hd tr0)). split; first by exact: mk_singleton_nil.
  apply follows_nil => // {h0}. move: H3 => [tr1 [h0 h1]]. exists tr1. split=>//.
  by apply: (follows_monotone (singleton_monotone _) h1).
Qed.

(* Corollary 4.1 *)
Lemma tsemax_correct_for_semax: forall s U V, tsemax U s V ->
 semax U s (Finite *** [| V |]).
Proof.
move => s U V htsemax.
move: (tsemax_correct_semax htsemax ttS) => {}htsemax.
apply: (semax_conseq _ _  htsemax); first by move=> st0 hU; split.
apply: (impT_conseq_L (@Append_assoc_R _ _ _)).
apply: Append_monotone_L => tr [tr1 [[st0 [h0 h2]] h1]].
by inv h1; inv h2.
Qed.
