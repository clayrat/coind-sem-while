From CoindSemWhile Require Import SsrExport Trace Language.

Add Relation trace bisim
reflexivity proved by bisim_reflexive
symmetry proved by bisim_symmetric
transitivity proved by bisim_transitive
as bisim_rel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition setoid (p: trace -> Prop) :=
forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1.
Definition assertS := state -> Prop.
Definition assertT := { p: trace -> Prop | setoid p}.

Definition assertS_and (u1 u2: assertS) := fun st =>  u1 st /\ u2 st.

Infix "andS" := assertS_and (at level 60, right associativity).

Definition assertT_and (p1 p2: assertT): assertT.
destruct p1 as [f0 h0]. destruct p2 as [f1 h1].
exists (fun tr => f0 tr /\ f1 tr).
move => tr0 [h2 h3] tr1 h4. split.
* by apply: (h0 _ h2 _ h4).
* by apply: (h1 _ h3 _ h4).
Defined.

Infix "andT" := assertT_and (at level 60, right associativity).

Definition assertT_or (p1 p2: assertT): assertT.
destruct p1 as [f0 h0]. destruct p2 as [f1 h1].
exists (fun tr => f0 tr \/ f1 tr).
move => tr0 [h2 | h2] tr1 h3.
- left. by apply: (h0 _ h2 _ h3).
- right. by apply: (h1 _ h2 _ h3).
Defined.

Infix "orT" := assertT_or (at level 60, right associativity).

Definition assertS_imp (u1 u2: assertS) := forall st, u1 st -> u2 st.

Infix "->>" := assertS_imp (at level 60, right associativity).

Lemma assertS_imp_refl: forall u, u ->> u.
Proof.
by move => u st0 h0.
Qed.

Definition satisfy (p:assertT) (tr: trace): Prop :=
let: exist f0 h0 := p in f0 tr.

Definition assertT_imp (p1 p2: assertT) :=
forall tr, satisfy p1 tr -> satisfy p2 tr.

Infix "=>>" := assertT_imp (at level 60, right associativity).

Lemma impT_conseq_L: forall p0 p1 q,
p0 =>> p1 -> p1 =>> q -> p0 =>> q.
Proof.
move=> [p0 hp0] [p1 hp1] [q hq] h0 h1 tr0 /= h2.
by apply: h1=>/=; apply: h0=>/=.
Qed.

Lemma impT_conseq_R: forall p q0 q1,
q0 =>> q1 -> p =>> q0 -> p =>> q1.
Proof.
move=>[p hp] [q0 hq0] [q1 hq1] h0 h1 tr0 /= h2.
by apply: h0=>/=; apply: h1=>/=.
Qed.

Lemma imp_andT: forall p q0 q1,
p =>> q0 -> p =>> q1 -> p =>> (q0 andT q1).
Proof.
move => [p hp] [q0 hq0] [q1 hq1] h0 h1 tr0 /= h2.
by split; [apply: h0|apply: h1].
Qed.

Definition ttS: assertS := fun st => True.
Definition ffS: assertS := fun st => False.

Definition ttt: trace -> Prop := fun tr => True.
Definition ttT: assertT.
exists ttt. by move => tr0 h0 tr1 h1.
Defined.

Lemma assertT_imp_refl: forall p, p =>> p.
Proof. by move => p tr0 h0. Qed.

Lemma satisfy_cont: forall p0 p1,
 p0 =>> p1 -> forall tr, satisfy p0 tr -> satisfy p1 tr.
Proof.
move=> [f0 h0] [f1 h1] h2 tr /= h3. by apply: (h2 _ h3).
Qed.

Lemma assertT_imp_trans: forall p q r, p =>> q -> q =>> r -> p =>> r.
Proof.
move => p q r h0 h1 tr0 h2.
by apply/(satisfy_cont h1)/(satisfy_cont h0).
Qed.

Lemma andS_left: forall u1 u2, (u1 andS u2) ->> u1.
Proof. move => u1 u2 st h1; by inversion h1. Qed.

Lemma andS_right: forall u1 u2, (u1 andS u2) ->> u2.
Proof. move => u1 u2 st h1; by inversion h1. Qed.

Lemma andS_cont: forall u1 u1' u2 u2',
u1 ->> u1' ->
u2 ->> u2' ->
(u1 andS u2) ->> (u1' andS u2').
Proof.
move => u1 u1' u2 u2' h1 h2 st [h3 h4].
by split; [apply: (h1 _ h3)|apply: (h2 _ h4)].
Qed.

Lemma orT_left: forall p1 p2, p1 =>> (p1 orT p2).
Proof.
move => [f1 hf1] [f2 hf2] tr /= h1. by left.
Qed.

Lemma orT_right: forall p1 p2, p2 =>> (p1 orT p2).
Proof.
move => [f1 hf1] [f2 hf2] tr /= h1. by right.
Qed.

Definition singleton (u:assertS): trace -> Prop :=
fun tr => exists st, u st /\ bisim tr (Tnil st).

Lemma singleton_setoid: forall u, setoid (singleton u).
Proof.
move => u tr0 [st0 [h0 h2]] tr1 h1.
inv h2. inv h1. exists st0.
by split; [apply: h0 | apply: bisim_reflexive].
Qed.

Lemma singleton_monotone: forall u v, u ->> v ->
forall tr, singleton u tr ->  singleton v tr.
Proof.
move => u v huv tr0 [st0 [h0 h1]]. inv h1.
exists st0.
by split; [ apply: (huv _ h0) | apply: bisim_reflexive].
Qed.

Lemma singleton_nil: forall u st,
singleton u (Tnil st) -> u st.
Proof. move => u st [st0 [h0 h1]]. by inv h1. Qed.

Lemma mk_singleton_nil: forall (u : state -> Prop) st,
u st -> singleton u (Tnil st).
Proof. move => u st h0. exists st. split=>//; apply bisim_reflexive. Qed.

(* Proposition 3.1: <U> is setoid *)
Definition Singleton (u: assertS): assertT.
exists (singleton u).
move => tr0 [st0 [h0 h1]] tr1 h2. inv h1. inv h2.
exists st0. by split=>//; apply: bisim_nil.
Defined.

Notation "[| p |]" := (Singleton p) (at level 80).

(* Proposition 3.2: <U> is monotone *)
Lemma Singleton_monotone: forall u v,
u ->> v -> [|u|] =>> [|v|].
Proof.
move => u v h0 tr0 [st0 [h1 h2]].
inv h2. exists st0.
by split; [ apply: (h0 _ h1) | apply: bisim_reflexive].
Qed.

Definition eval_true (a: expr): assertS  :=
fun st => is_true (a st).

Definition eval_false (a: expr): assertS :=
fun st => ~~ is_true (a st).

Definition dup (u: assertS): trace -> Prop :=
fun tr => exists st, u st /\ bisim tr (Tcons st (Tnil st)).

Lemma dup_cont: forall (u0 u1: assertS),
u0 ->> u1 ->
forall tr, dup u0 tr -> dup u1 tr.
Proof.
move => u0 u1 hu tr [st0 [h0 h1]]. inv h1. inv H1.
exists st0.
by split; [apply: (hu _ h0)|apply: bisim_reflexive].
Qed.

(* Proposition 3.1: <<U>> is setoid *)
Definition Dup (u: assertS): assertT.
exists (dup u).
move => tr0 [st0 [h0 h1]] tr1 h2.
inv h1. inv H1. inv h2. inv H2. exists st0.
by split =>//; apply: bisim_reflexive.
Defined.

Notation "<< p >>" := (Dup p) (at level 80).

(* Proposition 3.2: <<U>> is monotone *)
Lemma Dup_monotone: forall u v, u ->> v -> <<u>> =>> <<v>>.
Proof. move => u v h0 tr0 /=. by apply: dup_cont. Qed.

CoInductive follows (p: trace -> Prop): trace -> trace -> Prop :=
| follows_nil: forall st tr,
  hd tr = st -> p tr ->
  follows p (Tnil st) tr
| follows_delay: forall st tr tr',
  follows p tr tr' -> follows p (Tcons st tr) (Tcons st tr').

Lemma follows_hd: forall p tr0 tr1, follows p tr0 tr1 ->
hd tr0 = hd tr1.
Proof.
move => p tr0 tr1 h0. by inv h0; simpl.
Qed.

Lemma follows_setoid: forall (p: trace -> Prop)
(hp: forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1),
forall tr0 tr1, follows p tr0 tr1 ->
forall tr2, bisim tr0 tr2 -> forall tr3, bisim tr1 tr3 ->
follows p tr2 tr3.
Proof.
move => p hp.
cofix CIH => tr0 tr1 h0 tr2 h1 tr3 h2. inv h0.
- clear CIH. inv h1.
  have h0 := bisim_hd h2. symmetry in h0.
  by apply: (follows_nil h0 (hp _ H0 _ h2)).
- inv h2. inv h1. by apply: (follows_delay st (CIH _ _ H _ H4 _ H3)).
Qed.

Lemma follows_setoid_L: forall p,
forall tr0 tr1, follows p tr0 tr1 ->
forall tr2, bisim tr0 tr2 ->  follows p tr2 tr1.
Proof.
move => p. cofix CIH=>tr tr0 h0 tr1 h1. inv h0; inv h1.
- by apply: follows_nil.
- by apply: (follows_delay st (CIH _ _ H _ H3)).
Qed.

Lemma follows_setoid_R: forall (p: trace -> Prop)
(hp: forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1),
forall tr tr0, follows p tr tr0 ->
forall tr1, bisim tr0 tr1 ->  follows p tr tr1.
Proof.
move => p hp.
cofix CIH=> tr tr0 h0 tr1 h1. inv h0.
- apply/follows_nil.
  - by apply/esym/bisim_hd.
  by apply: (hp _ H0 _ h1).
- inv h1. by apply: (follows_delay st (CIH _ _  H _ H3)).
Qed.

Lemma follows_monotone: forall (p q : trace -> Prop),
(forall tr, p tr -> q tr) ->
forall tr0 tr1, follows p tr0 tr1 -> follows q tr0 tr1.
Proof.
move => p q hpq. cofix CIH=> tr0 tr1 h0. inv h0.
- apply: follows_nil => //. by apply: (hpq _ H0).
- by apply/follows_delay/CIH.
Qed.

(* Lemma 3.2 *)
Lemma follows_singleton: forall u tr0 tr1,
follows (singleton u) tr0 tr1 -> bisim tr0 tr1.
Proof.
move => u. cofix CIH=> tr0 tr1 h0. inv h0.
- move: H0 => [st0 [h0 h1]]. inv h1. by apply: bisim_reflexive.
- by apply: (bisim_cons st (CIH _ _ H)).
Qed.

Lemma follows_singleton_andS_L: forall u0 u1 tr0,
follows (singleton (u0 andS u1)) tr0 tr0 ->
follows (singleton u0) tr0 tr0.
Proof.
move => u0 u1. cofix CIH. case=> st0.
- move =>h0. inversion h0. clear H1 H. simpl in H0.
  inv h0.
  move: H3 => [st1 [h1 h2]]. inv h2. move: h1 => [h1 h2].
  apply follows_nil => //. exists st1. by split=>//; apply: bisim_reflexive.
- move => tr0 h0. inv h0.
  by apply/follows_delay/CIH.
Qed.

Lemma follows_singleton_andS_R: forall u0 u1 tr0,
follows (singleton (u0 andS u1)) tr0 tr0 ->
follows (singleton u1) tr0 tr0.
Proof.
move => u0 u1. cofix CIH. case.
- move => st0 h0. inversion h0=>{H1 H}. simpl in H0.
  inv h0.
  move: H3 => [st1 [h1 h2]]. inv h2. move: h1 => [h1 h2].
  apply follows_nil => //. exists st1. by split=>//; apply: bisim_reflexive.
- move => st0 tr0 h0. inv h0.
  by apply: (follows_delay st0 (CIH _ H0)).
Qed.

Lemma singleton_andS_follows: forall u v tr,
follows (singleton u) tr tr -> follows (singleton v) tr tr ->
follows (singleton (u andS v)) tr tr.
Proof.
move => u v. cofix CIH=> tr h0 h1. inversion h0; subst.
- apply follows_nil => //. exists st. split; last by apply: bisim_reflexive.
  clear H. inversion h1; subst. clear H1.
  by split; [exact: singleton_nil H0|exact: singleton_nil H2].
- subst. inv h0. inv h1. by apply: (follows_delay st (CIH _ H1 H2)).
Qed.

CoFixpoint lastdup (tr: trace): trace :=
match tr with
| Tnil st => Tcons st (Tnil st)
| Tcons st tr' => Tcons st (lastdup tr')
end.

Lemma lastdup_hd: forall tr, hd tr = hd (lastdup tr).
Proof.
case=>st.
- by rewrite [lastdup _]trace_destr /=.
- move => tr. by rewrite [lastdup _]trace_destr /=.
Qed.

Lemma follows_dup: forall u tr, follows (singleton u) tr tr ->
follows (dup u) tr (lastdup tr).
Proof.
move => u. cofix CIH=> tr0 h0. inversion h0.
- clear H H1 H2 h0. rewrite [lastdup _]trace_destr /=.
  move: H0 => [st1 [h0 h1]]. inv h1. apply follows_nil => //. exists st1.
  by split=>//; apply: bisim_reflexive.
- clear h0 H0 H. rewrite [lastdup _]trace_destr /=.
  by apply: (follows_delay st (CIH _ H1)).
Qed.

Definition append (p1 p2: trace -> Prop ): trace -> Prop :=
fun tr => exists tr', p1 tr' /\ follows p2 tr' tr.

Infix "*+*" := append (at level 60, right associativity).

Lemma append_cont: forall (p0 p1 q0 q1: trace -> Prop),
(forall tr, p0 tr -> p1 tr) ->
(forall tr, q0 tr -> q1 tr) ->
forall tr, append p0 q0 tr -> append p1 q1 tr.
Proof.
move => p0 p1 q0 q1 hp hq tr [tr0 [h0 h1]].
exists tr0. split; first by apply: (hp _ h0).
clear h0.
move: tr0 tr h1. cofix CIH=> tr0 tr1 h0. inv h0.
- apply follows_nil => //. by apply: (hq _ H0).
- by apply/follows_delay/CIH.
Qed.

Lemma append_cont_L: forall (p0 p1 q: trace -> Prop),
(forall tr, p0 tr -> p1 tr) ->
forall tr, (append p0 q tr) -> (append p1 q tr).
Proof.
move => p0 p1 q hp tr [tr0 [h0 h1]].
exists tr0. by split=>//; apply: (hp _ h0).
Qed.

Lemma append_monotone_R: forall (p q0 q1: trace -> Prop),
(forall tr, q0 tr -> q1 tr) ->
forall tr, (append p q0 tr) -> (append p q1 tr).
Proof.
move => p q0 q1 hq. by apply: (@append_cont p p _ _ _ hq).
Qed.

Lemma append_setoid: forall (p0 p1: trace -> Prop),
setoid p1 -> setoid (append p0 p1).
Proof.
move => p0 p1 hp1 tr0 [tr2 [h0 h2]] tr1 h1.
exists tr2. split; first by apply h0.
by apply: (follows_setoid_R hp1 h2 h1).
Qed.

Lemma follows_follows: forall p q tr0 tr1 tr2, follows p tr0 tr1 ->
follows q tr1 tr2 -> follows (p *+* q) tr0 tr2.
Proof. move => p q. cofix CIH. case.
- move => st0 tr1 tr2 h0 h1. inv h0.
  have h2 := follows_hd h1.
  apply follows_nil => //. by exists tr1.
- move => st0 tr0 tr1 tr2 h0 h1. inv h0. inv h1.
  by apply/follows_delay/(CIH _ _ _ H2).
Qed.

CoInductive midp (p0 p1: trace -> Prop) (tr0 tr1: trace) (h: follows (append p0 p1) tr0 tr1) : trace -> Prop :=
| midp_follows_nil :
   forall tr, tr0 = Tnil (hd tr1) -> p0 tr -> follows p1 tr tr1 -> midp h tr
| midp_follows_delay :
  forall (tr2 tr3 :trace) (h1: follows (append p0 p1) tr2 tr3) (st : state) tr',
  tr0 = Tcons st tr2 -> tr1 = Tcons st tr3 -> @midp p0 p1 tr2 tr3 h1 tr' ->
  midp h (Tcons st tr').

Lemma midp_before: forall p0 p1 tr0 tr1 (h: follows (append p0 p1) tr0 tr1) tr',
midp h tr' ->
follows p0 tr0 tr'.
Proof.
cofix CIH. dependent inversion h. move => {tr H0}.
- move: tr1 st tr0 h e a H. case.
  - move => st0 st1 tr0 h1 /= h2 h3 h4 tr' hm.
    inv hm; last by inversion H.
    destruct h3. destruct H2. inversion h1.
    subst. apply: follows_nil =>//.
    by inversion H1.
  - move => st0 tr0 st1 tr1 h1 /= h2 h3 h4 tr' hm.
    inv hm; last by inversion H.
    destruct h3. destruct H2. inversion h1.
    subst. apply: follows_nil=>//. by inversion H1.
- subst.
  move => tr0 hm.
  destruct tr0; first by inversion hm.
  inv hm; subst; first by inversion H.
  inv H1; subst.
  inv H2; subst.
  by apply/follows_delay/(CIH _ _ _ _ h1).
Qed.

Lemma midp_after: forall p0 p1 tr0 tr1 (h: follows (append p0 p1) tr0 tr1) tr',
midp h tr' ->
follows p1 tr' tr1.
Proof.
cofix CIH. dependent inversion h. move => {tr H0}.
- move: tr1 st tr0 h e a H. case.
  * move => st0 st1 tr0 h1 /= h2 h3 h4 tr' hm.
    inv hm; last by inversion H. destruct tr'; last by inversion H.
    destruct h3. destruct H2. inversion H3. subst.
    apply: follows_nil=>//. by inversion H1.
  * move => st0 tr0 st1 tr1 h1 /= h2 h3 h4 tr' hm.
    inv hm; by inversion H.
subst.
move => tr0 hm.
destruct tr0; first by inversion hm.
inv hm; subst; first by inversion H.
inv H1; subst.
inv H2; subst.
by apply/follows_delay/(CIH _ _ _ _ h1).
Qed.

Lemma append_assoc_L: forall p1 p2 p3 tr,
(append (append p1 p2) p3) tr -> append p1 (append p2  p3) tr.
Proof.
move => p1 p2 p3 tr0 [tr1 [[tr2 [h1 h3]] h2]].
exists tr2. split=>// {h1}.
move: tr2 tr0 tr1 h2 h3. cofix CIH=> tr0 tr1 tr2 h1 h2. inv h2.
- apply/follows_nil; first by apply/esym/follows_hd/h1.
  by exists tr2.
- inv h1. by apply/follows_delay/(CIH _ _ _ H3).
Qed.

(* Proposition 3.1: ** is setoid. *)
Definition Append (p1 p2: assertT): assertT.
destruct p1 as [f0 h0]. destruct p2 as [f1 h1].
exists (append f0 f1).
move => tr0 [tr1 [h2 h3]] tr2 h4. exists tr1.
split=>//. by apply: (follows_setoid_R h1 h3 h4).
Defined.

Infix "***" := Append (at level 60, right associativity).

(* Lemma 3.4 (4) => *)
Lemma Append_assoc_L: forall p1 p2 p3,
((p1 *** p2) *** p3) =>> (p1 *** p2 *** p3).
Proof.
move => [f1 hf1] [f2 hf2] [f3 hf3] tr0 /= h1.
by apply: append_assoc_L.
Qed.

(* Proposition 3.2: ** is monotone *)
Lemma Append_monotone: forall p1 p2 q1 q2,
p1 =>> p2 -> q1 =>> q2 -> (p1 *** q1) =>> (p2 *** q2).
Proof.
move=> [p1 hp1] [p2 hp2] [q1 hq1] [q2 hq2] h0 h1 tr0 /= h2.
by apply: (append_cont _ _ h2).
Qed.

Lemma Append_monotone_L: forall p1 p2 q,
p1 =>> p2 -> (p1 *** q) =>> (p2 *** q).
Proof.
move=> [p1 hp1] [p2 hp2] [q hq] h0 tr0 /=.
by apply: append_cont_L.
Qed.

Lemma Append_monotone_R: forall q p1 p2,
p1 =>> p2 -> (q *** p1) =>> (q *** p2).
Proof.
move => [q hq] [p1 hp1] [p2 hp2] h0 tr0 /= h1.
by apply: (@append_cont q q p1 p2).
Qed.

Lemma Append_ttS: forall p,
p =>> (p *** [| ttS |]).
Proof.
move => [f hp] tr0 /= h0. exists tr0.
split=>// {h0 hp}. move: tr0. cofix CIH. case=>st0.
- apply: follows_nil => //; by apply mk_singleton_nil.
move=>tr0.
by apply/follows_delay/CIH.
Qed.

(* Lemma 3.4 (1), the first => *)
Lemma Sglt_Dup_1: forall u v, ([|u|] *** <<v>>) =>> <<u andS v>>.
Proof.
move=>u v tr0 [tr1 [[st0 [h0 h2]] h1]] /=. inv h2. inv h1.
destruct H1 as [st0 [h1 h2]]. inv h2. inv H1. simpl in h0. exists st0.
by split=>//; apply: bisim_reflexive.
Qed.

(* Lemma 3.4 (1), the first <= *)
Lemma Sglt_Dup_2: forall u v, <<u andS v>> =>> ([|u|] *** <<v>>).
Proof.
move => u v tr0 [st0 [[hu hv] h1]]. inv h1. inv H1. exists (Tnil st0). split.
* exists st0. by split=>//; apply: bisim_reflexive.
* apply follows_nil => //. exists st0. by split=>//; apply: bisim_reflexive.
Qed.

(* Lemma 3.4 (1), the second => *)
Lemma Sglt_Dup_3: forall u v, <<u andS v>> =>> <<u>> *** [|v|].
Proof.
move => u v tr0 [st0 [[hu hv] h0]]. inv h0. inv H1. exists (Tcons st0 (Tnil st0)).
split.
- exists st0. by split=>//; apply: bisim_reflexive.
apply/follows_delay/follows_nil => //. exists st0.
by split=>//; apply: bisim_reflexive.
Qed.

(* Lemma 3.4 (1), the second <= *)
Lemma Sglt_Dup_4: forall u v, (<<u>> *** [|v|]) =>> <<u andS v>>.
Proof.
move => u v tr0 [tr1 [[st0 [hu h0]] h1]]. inv h0. inv H1.
inv h1. inv H2. destruct H1 as [st0 [hv h0]]. inv h0. simpl in hu. simpl.
exists st0. by split=>//; apply: bisim_reflexive.
Qed.

(* Lemma 3.4 (2), => *)
Lemma Sglt_Chop_1: forall u v, ([|u|] *** [|v|]) =>> [|u andS v|].
Proof.
move => u v tr0 [tr1 [[st0 [hu h0]] h1]]. inv h0.
inv h1. destruct H1 as [st0 [hv h0]]. inv h0. simpl in hu. exists st0.
by split=>//; apply: bisim_reflexive.
Qed.

(* Lemma 3.4 (2), <= *)
Lemma Sglt_Chop_2: forall u v, [|u andS v|] =>> [|u|] *** [|v|].
Proof.
move => u v tr0 [st0 [[hu hv] h0]]. inv h0. exists (Tnil st0).
split.
- exists st0. by split=>//; apply: bisim_reflexive.
apply: follows_nil => //.
exists st0. by split=>//; apply: bisim_reflexive.
Qed.

Lemma Singleton_Append: forall v p, ([|v|] *** p) =>> p.
Proof.
move => v [p hp] tr0 /= [tr1 [[st0 [h0 h2]] h1]].
inv h2. by inv h1.
Qed.

(* Lemma 3.4 (3), the first => *)
Lemma ttS_Chop: forall p,
([|ttS|] *** p) =>> p.
Proof. move => p. by apply Singleton_Append. Qed.

(* Lemma 3.4 (3), the first <= *)
Lemma ttS_Chop_2: forall p,  p =>> [|ttS|] *** p.
Proof.
move => [p hp] tr0 /= htr0. exists (Tnil (hd tr0)). split.
- exists (hd tr0). by split=>//; apply: bisim_reflexive.
by exact: follows_nil.
Qed.

Lemma append_singleton: forall p (hp: setoid p) u tr,
append p (singleton u) tr -> p tr.
Proof.
move => p hp u tr0 [tr1 [h1 h2]].
by apply/(hp _ h1)/(follows_singleton h2).
Qed.

Lemma Append_Singleton: forall p v, (p *** [|v|]) =>> p.
Proof. move => [p hp] v tr0 /=. by apply append_singleton. Qed.

(* Lemma 3.4 (3), the second <= *)
Lemma Chop_ttS: forall p, (p *** [|ttS|]) =>> p.
Proof. move => p. by apply Append_Singleton. Qed.

(* Lemma 3.4 (3), the second => *)
Lemma Chop_ttS_2: forall p, p =>> p *** [|ttS|].
Proof.
move => [p hp] tr0 /= htr0. exists tr0; split=>// {hp htr0}.
move: tr0. cofix CIH. case=>st0.
- apply follows_nil=>//. exists st0. by split=>//; apply: bisim_reflexive.
- by move=>tr0; apply/follows_delay/CIH.
Qed.

Lemma ttT_idem_comp: (ttT *** ttT) =>> ttT.
Proof. by []. Qed.

Inductive finite: trace -> Prop :=
| finite_nil: forall st, finite (Tnil st)
| finite_delay: forall st tr,
  finite tr -> finite (Tcons st tr).

Lemma finite_setoid: forall tr, finite tr ->
forall tr0, bisim tr tr0 -> finite tr0.
Proof.
induction 1=>tr0 h0; inv h0.
- by apply: finite_nil.
- by apply/finite_delay/IHfinite.
Qed.

(* Proposition 3.1: finite is setoid. *)
Definition Finite: assertT.
exists (fun tr => finite tr).
move => tr0 h0 tr1 h1.
apply: (finite_setoid h0 h1).
Defined.

Lemma Finite_idem_1: (Finite *** Finite) =>> Finite.
Proof.
move => tr0 [tr1 [h0 h1]]. move: tr1 h0 tr0 h1. induction 1=>tr0.
- move => h0. by inv h0.
- move => h1. inv h1.
  by apply/finite_delay/IHh0.
Qed.

Lemma Finite_idem_2: Finite =>> Finite *** Finite.
Proof.
move => tr0 h0 /=; exists (Tnil (hd tr0)).
by split; [apply: finite_nil|apply: follows_nil].
Qed.

Lemma Finite_singleton: forall u, (Finite *** [|u|]) =>> Finite.
Proof.
move => u tr /= [tr1 [h0 h1]].
by apply/(finite_setoid h0)/follows_singleton/h1.
Qed.

CoInductive iter (p: trace -> Prop): trace -> Prop :=
| iter_stop: forall st, iter p (Tnil st)
| iter_loop: forall tr tr0,
  p tr ->
  follows (iter p) tr tr0 ->
  iter p tr0.

Lemma iter_setoid: forall p (hp: setoid p), setoid (iter p).
Proof.
move => p hp. cofix CIH.
have h0: forall tr, setoid (follows (iter p) tr).
* cofix COINDHYP1=> tr tr0 h0 tr1 h1. inv h0.
  - apply: follows_nil; first by apply/esym/bisim_hd.
    by apply: (CIH _ H0 _ h1).
  - inv h1. by apply: (follows_delay st (COINDHYP1 _ _ H _ H3)).
* move => tr0 h1 tr1 h2. inv h1.
  - inv h2. by apply: iter_stop.
  - by apply: (iter_loop H (h0 _ _ H0 _ h2)).
Qed.

Lemma iter_cont: forall (p0 p1: trace -> Prop),
(forall tr, p0 tr -> p1 tr) ->
forall tr, iter p0 tr -> iter p1 tr.
Proof.
move => p0 p1 hp. cofix CIH.
have h: forall tr0 tr1, follows (iter p0) tr0 tr1 -> follows (iter p1) tr0 tr1.
* cofix COINDHYP0=> tr0 tr1 h0. inv h0.
  - apply follows_nil=>//. by apply: CIH.
  - by apply: (follows_delay st (COINDHYP0 _ _ H)).
* move => tr0 h0. inv h0.
  - apply iter_stop.
  - by apply: (iter_loop (hp _ H)  (h _ _ H0)).
Qed.

Lemma iter_append_dup: forall (u : state -> Prop) p tr,
u (hd tr) -> iter (append p (dup u)) tr ->
follows (singleton u) tr tr.
Proof.
move => u p. cofix CIH=> tr h0 h1. inv h1.
- simpl in h0. apply follows_nil => //. exists st.
  by split=>//; apply: bisim_reflexive.
- move: H => [tr1 [h2 h1]]. clear h2 h0. (*
  have h2 := follows_hd X0.  rewrite -h2 in h0 => {h2}.   *)
  move: tr tr1 tr0 h1 H0.
  cofix hcoind1=> tr0 tr1 tr2 h0 h1. inv h0.
  - move: H0 => [st0 [h0 h3]]. inv h3. inv H1.
    inv h1. inv H2. by apply: (follows_delay _ (CIH _ h0 H1)).
  - inv h1. by apply: (follows_delay _ (hcoind1 _ _ _ H H3)).
Qed.

(* Proposition 3.2: Iter is setoid. *)
Definition Iter (p: assertT): assertT.
destruct p as [f0 h0].
exists (iter f0). by apply: iter_setoid.
Defined.

(* Proposition 3.2: Iter is monotone. *)
Lemma Iter_monotone: forall p q, p =>> q -> (Iter p) =>> (Iter q).
Proof.
move => [p hp] [q hq] h0 tr0 /=.
apply: iter_cont=> tr1. apply: h0.
Qed.

Definition updt (u: assertS) (x:id) (a: expr): trace -> Prop :=
fun tr => exists st, u st /\ bisim tr (Tcons st (Tnil (update x (a st) st))).

(* Proposition 3.1: U[x↦e] is setoid. *)
Definition Updt (u: assertS) (x:id) (a: expr): assertT.
exists (updt u x a).
move => tr0 [st0 [h0 h1]] tr1 h2.
exists st0. inv h1. inv H1. inv h2. inv H2.
by split=>//; apply: bisim_reflexive.
Defined.

Definition exS (A: Type) (u: A -> assertS) : assertS :=
fun st => exists x, u x st.

Definition exT (A: Type) (p: A -> assertT) : assertT.
exists (fun tr => exists x, satisfy (p x) tr).
move => tr0 [x h0] tr1 h1. exists x. destruct (p x) as [f0 h2].
simpl. simpl in h0. by apply: (h2 _ h0 _ h1).
Defined.

Definition negT (p: assertT): assertT.
destruct p as [f hf].
exists (fun tr => f tr -> False).
move => tr0 h0 tr1 h1 /= h2.
by move: (hf _ h2 _ (bisim_symmetric h1)).
Defined.

CoInductive infinite: trace -> Prop :=
| infinite_delay: forall st tr,
  infinite tr -> infinite (Tcons st tr).

(* Proposition 3.1: Infinite is setoid. *)
Definition Infinite: assertT.
exists (fun tr => infinite tr).
move => tr0 /= h0 tr1 h1.
move: tr0 h0 tr1 h1. cofix CIH => tr0 h0 tr1 h1.
inv h0. inv h1. by apply: (infinite_delay st (CIH _ H _ H3)).
Defined.

(* Lemma 3.4 (7), => *)
Lemma infinite_implies_true_chop_false: Infinite =>> (ttT *** [|ffS|]).
Proof.
move => tr0 [st0 tr1] hinfinite /=. exists (Tcons st0 tr1). split => // {tr0}.
move: st0 tr1 hinfinite.
cofix hcofix=> st0 tr0 h. apply follows_delay. inversion h. subst.
by apply/hcofix/H.
Qed.

(* Lemma 3.4 (7), <= *)
Lemma true_chop_false_implies_infinite: (ttT *** [|ffS|]) =>> Infinite.
Proof.
move => tr0 [tr1 [_ h1]] /=.
move: tr0 tr1 h1. cofix h0 => tr0 tr1 h1.
inv h1.
- destruct H0 as [st0 [h1 h2]]. by inversion h1.
- by apply/infinite_delay/(h0 _ _ H).
Qed.

(* extensions *)
Lemma iter_split_1: forall p tr, iter p tr -> (singleton ttS tr) \/ (append p (iter p) tr).
Proof.
move => p tr h0. inv h0.
- left. exists st. by split => //; apply: bisim_reflexive.
- right. by exists tr0.
Qed.

(* Lemma 3.4 (5), => *)
Lemma Iter_unfold_0: forall p, Iter p =>> ([|ttS|] orT (p *** Iter p)).
Proof.
move => [p hp] tr0 /= h0.
by apply: iter_split_1.
Qed.

Lemma iter_split_2: forall tr p, (singleton ttS tr) \/ (append p (iter p) tr) -> iter p tr.
Proof.
move => tr p h. inv h.
- move: H => [st [h0 h1]]. inv h1. by apply: iter_stop.
- move: H => [tr0 [h0 h1]]. by apply: (iter_loop h0 h1).
Qed.

(* Lemma 3.4 (5), <= *)
Lemma Iter_fold_0: forall p, ([|ttS|] orT (p *** Iter p)) =>> Iter p.
Proof. move => [p hp] tr0 /=. by apply: iter_split_2. Qed.

Lemma iter_unfold_1: forall p tr, (iter p *+* p) tr -> iter p tr.
Proof.
move => p tr [tr0 [h0 h1]].
move: tr0 tr h0 h1. cofix CIH=> tr0 tr1 h0 h1. inv h0.
- inv h1. apply: (iter_loop H1) => {H1}. move: tr1. cofix CIH0.
  case.
  * move => st. apply: follows_nil => //. by apply: iter_stop.
  move => st0 tr0. by apply/follows_delay/CIH0.
- apply: (iter_loop H) => {H}. move: tr tr0 tr1 H0 h1.
  cofix CIH0 => tr0 tr1 tr2 h0 h1. inv h0.
  - have h0 := follows_hd h1. apply follows_nil => //.
    by apply: (CIH _ _ H0 h1).
  - inv h1. by apply/follows_delay/(CIH0 _ _ _ H H3).
Qed.

Lemma Iter_unfold_1: forall p, (Iter p *** p) =>> Iter p.
Proof.
move => [p hp] tr /= h0.
by apply: iter_unfold_1.
Qed.

Lemma Iter_unfold_2: forall p, ([|ttS|] orT (Iter p *** p)) =>> Iter p.
Proof.
move=> [p hp] tr0 /= h0. inv h0.
- move: H => [st0][_]h0. inv h0. by apply: iter_stop.
by apply: iter_unfold_1.
Qed.

Lemma Stop_Iter: forall p, [|ttS|] =>> Iter p.
Proof.
move => [p hp] /= t0 h0. inv h0.
move: H => [_ h0]. inv h0. simpl. by apply: iter_stop.
Qed.

Lemma Iter_fold_L: forall p, (p *** Iter p) =>> Iter p.
Proof.
move => [p hp] tr0 /= [tr1][h0]h1.
by apply: (iter_loop h0).
Qed.

Lemma iter_iter_2: forall p tr, iter p tr -> append (iter p) (iter p) tr.
Proof.
move => p tr0 h0. exists tr0. split => // {h0}. move: tr0.
cofix CIH. case=> st0.
- apply follows_nil => //. by apply iter_stop.
- move => tr0. by apply/follows_delay/CIH.
Qed.

(* Lemma 3.4 (6), => *)
Lemma Iter_Iter_2: forall p, Iter p =>> (Iter p *** Iter p).
Proof. move => [p hp] tr0 /=. by apply: iter_iter_2. Qed.

Lemma iter_iter: forall p tr, append (iter p) (iter p) tr -> (iter p) tr.
Proof.
move => p tr0 [tr1 [h0 h1]]. move: tr1 tr0 h0 h1.
cofix CIH=> tr0 tr1 h0. inv h0=>h0.
- by inv h0.
- apply: (iter_loop H) => {H}. move: tr tr0 tr1 H0 h0.
  cofix CIH2=> tr0 tr1 tr2 h0. inv h0=>h0.
  - apply: follows_nil; first by apply/esym/(follows_hd h0).
    by apply: (CIH _ _ H0).
  - inv h0. by apply/follows_delay/(CIH2 _ _ _ H).
Qed.

(* Lemma 3.4. (6), <= *)
Lemma Iter_Iter: forall p, (Iter p *** Iter p) =>> Iter p.
Proof. move => [p hp] tr /=. by apply: iter_iter. Qed.

(* Lemma 3.1 *)
Lemma follows_ttS: forall tr, follows (singleton ttS) tr tr.
Proof.
cofix CIH. case=> st0.
- apply follows_nil => //. exists st0.
  by split => //; apply: bisim_reflexive.
- move => tr0. by apply/follows_delay/CIH.
Qed.

Inductive fin: trace -> state -> Prop :=
| fin_nil: forall st, fin (Tnil st) st
| fin_delay: forall st st' tr, fin tr st' -> fin (Tcons st tr) st'.

Lemma append_fin: forall (p q : trace -> Prop) tr0 tr1, p tr0 -> q tr1 -> fin tr0 (hd tr1) ->
(p *+* q) (tr0 +++ tr1).
Proof.
move => p q tr0 tr1 hp hq hfin. exists tr0. split => // {hp}.
move: tr0 tr1 hq hfin. cofix CIH. case=> st0 tr0.
- move => hq h1. rewrite trace_append_nil. inv h1. by apply: follows_nil.
- move => tr1 h0 h1. inv h1. rewrite [Tcons st0 tr0 +++ tr1]trace_destr /=.
  by apply/follows_delay/(CIH _ _ h0).
Qed.

Definition last (p: trace -> Prop): assertS :=
fun st => exists tr, (p tr) /\ (fin tr st).

Lemma last_cont: forall (p q: trace -> Prop),
(forall tr, p tr -> q tr) ->
last p ->> last q.
Proof.
move => p0 p1 hp st [tr [h0 h1]].
exists tr. split=>//. by apply: hp.
Qed.

Definition Last (p: assertT): assertS.
move: p => [f0 h0]. by apply (last f0).
Defined.

(* Proposition 3.2: Last is monotone. *)
Lemma Last_monotone: forall p q,
p =>> q -> Last p ->> Last q.
Proof.
move=> [f hf] [g hg] /= h0.
by apply/last_cont/h0.
Qed.

(* Lemma 3.4 (10), => *)
Lemma Last_Singleton_fold: forall u, Last ([|u|]) ->> u.
Proof.
move => u st0 [tr0] [[st1 [h1 h3]] h2].
by inv h3; inv h2.
Qed.

(* Lemma 3.4 (10), <= *)
Lemma Last_Singleton_unfold: forall u, u ->> Last ([|u|]).
Proof.
move => u st0 h0. exists (Tnil st0). split.
- exists st0. by split=>//; apply: bisim_nil.
- by apply: fin_nil.
Qed.


(* Lemma 3.4, (11) *)
Lemma last_chop: forall p q st, last (append p q) st -> last q st.
Proof.
move => p q st [tr0] [[tr [_ h2]] h1].
move: tr0 st h1 tr h2. induction 1=> tr0 h0; inv h0.
- exists (Tnil st). by split=>//; apply: fin_nil.
- exists (Tcons st tr). by split=>//; apply: (fin_delay _ h1).
- by apply: (IHh1 _ H1).
Qed.

(* Lemma 3.4, (13) *)
Lemma Last_chop_sglt: forall p v,
Last (p *** [|v|]) ->> v.
Proof.
move => [p hp] v /= st [tr [[tr' [_ h0]] h1]].
move: tr st h1 tr' h0. induction 1=> tr0 h0; inv h0.
- move: H0 => [st0 [h0 h1]]. by inv h1.
- move: H0 => [st0 [_ h0]]. by inv h0.
- by apply: (IHh1 _ H1).
Qed.

Lemma Last_andS: forall p u, ((Last p) andS u) ->> Last (p *** [|u|]).
Proof.
move => [p hp] u st0 [/= [tr0 [h2 h3]] h1].
exists tr0. split=>//. exists tr0. split=>// {h2}.
move: tr0 st0 h3 h1. cofix CIH=> tr0 st0 h0. inv h0=> h0.
- apply follows_nil => //. exists st0. by split=>//; apply: bisim_reflexive.
- by apply/follows_delay/(CIH _ _ H).
Qed.

Lemma iter_last: forall v,
([|v|] *** (Iter (ttT *** Dup v))) =>> (ttT *** [|v|]).
Proof.
move => v tr0 [tr1 [[st0 [h0 h2]] h1]]. inv h2.
inv h1. simpl. exists tr0. split => //. move: tr0 h0 H1.
cofix CIH=> tr0 h0 h1. inv h1.
- apply follows_nil => //. simpl in h0. exists st.
  by split=>//; apply: bisim_nil.
- clear h0. move: H => [tr1 [_ h1]]. move: tr1 tr tr0 h1 H0.
  cofix CIH0=> tr0 tr1 tr2 h0 h1. inv h0.
  - move: H0 => [st0 [h0 h2]]. inv h2. inv H1. inv h1. inv H2.
    by apply/follows_delay/(CIH _ h0).
  - inv h1. by apply/follows_delay/(CIH0 _ _ _ H).
Qed.

(* Lemma 3.4, (14) *)
Lemma Last_Sglt_Iter: forall v p,
Last ([|v|] *** (Iter (p *** Dup v))) ->> v.
Proof.
move => v p st0 h0.
have h1: p =>> ttT by done.
have {}h0 := Last_monotone (Append_monotone_R (Iter_monotone (Append_monotone_L
h1))) h0 => {h1}.
move: (Last_monotone (@iter_last v) h0) => {h0}.
by apply: Last_chop_sglt.
Qed.

Lemma iter_last_dup: forall v,
(<<v>> *** (Iter (ttT *** <<v>>))) =>> (ttT *** [|v|]).
Proof.
move=> v tr0 [tr1 [[st0 [h0 h2]] h1]].
inv h2. inv H1. inv h1. inv H2. simpl.
exists (Tcons (hd tr') tr'). split => //.
apply follows_delay => //. move: tr' h0 H1.
cofix CIH=> tr0 h0 h1. inv h1.
- apply follows_nil => //. simpl in h0. exists st.
  by split => //; apply: bisim_nil.
- clear h0. move: H => [tr1 [_ h1]]. move: tr1 tr tr0 h1 H0.
  cofix CIH0=> tr0 tr1 tr2 h0 h1. inv h0.
  - move: H0 => [st0 [h0 h2]]. inv h2. inv H1. inv h1. inv H2.
    by apply/follows_delay/(CIH _ h0).
  - inv h1. by apply/follows_delay/(CIH0 _ _ _ H).
Qed.

(* Lemma 3.4, (12) *)
Lemma Last_Last: forall p q,
(Last ([| Last p |] *** q)) ->> (Last (p *** q)).
Proof.
move => [p hp] [q hq] st0 /= [tr1 [[tr0 [[tr2 [h0 h3]] h2]] h1]].
inv h3. inv h2. move: h0 => [tr2 [h0 h2]].
exists (tr2 +++ tr1). split.
* exists tr2. split => // {h0 h1}.
  move: tr2 h2. cofix CIH. case.
  - move => st1 h0. rewrite trace_append_nil.
    apply follows_nil => //. by inv h0.
  - move => st1 tr0 h0. inv h0. rewrite trace_append_cons.
    by apply/follows_delay/(CIH _ H3).
* clear H1 h0. move h0: (hd tr1) => st1. rewrite h0 in h2.
  move: tr2 st1 h2 tr1 h0 h1. induction 1=> tr0 h0 h1.
  - by rewrite trace_append_nil.
  - rewrite trace_append_cons.
    by apply/fin_delay/(IHh2 _ h0 h1).
Qed.

Lemma singleton_andS_append: forall u v,
(v andS u) ->> Last ([|v|] *** [|u|]).
Proof.
move => u v st0 [h0 h1]. exists (Tnil st0). split.
* exists (Tnil st0). split.
  - exists st0. by split => //; apply bisim_reflexive.
  - apply: follows_nil=>//. exists st0. by split => //; apply: bisim_reflexive.
* by apply: fin_nil.
Qed.

Lemma fin_lastdup: forall tr st, fin tr st -> fin (lastdup tr) st.
Proof.
induction 1; rewrite [lastdup _]trace_destr /=.
- by apply/fin_delay/fin_nil.
- by apply: fin_delay.
Qed.

Lemma Last_dup: forall p u, Last (p *** [|u|]) ->> Last (p *** <<u>>).
Proof.
move => [p hp] u st0 [tr0 [[tr1 [h0 h2]] h1]].
exists (lastdup tr0). split.
* have h3 := follows_singleton h2.
  have h4 := follows_setoid (@singleton_setoid _) h2 h3 (bisim_reflexive _) => {h2}.
  exists tr0. split.
  - by apply: (hp _ h0 _ h3).
  - by apply: (follows_dup h4).
* by apply: (fin_lastdup h1).
Qed.

Lemma hd_append: forall tr0 st0, fin tr0 st0 -> forall tr1,
hd tr1 = st0 -> hd (tr0 +++ tr1) = hd tr0.
Proof.
induction 1=> tr0 h0.
- by rewrite trace_append_nil.
- by rewrite trace_append_cons.
Qed.
