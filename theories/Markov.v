From CoindSemWhile Require Import SsrExport Trace Language Assert Semax.
From Coq Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable B : nat -> Prop.
Axiom B_noncontradictory : ~ (forall n, ~ B n).
Variable x : id.
Variable cond : expr.
Axiom cond_true : forall st, eval_true cond st -> ~ B (st x).
Axiom cond_false : forall st, eval_false cond st -> B (st x).

Definition x_is_zero : assertS := fun st => st x = 0.
Definition B_holds_for_x : assertS := fun st => B (st x).
Definition incr_x : expr := fun st => st x + 1.

CoInductive cofinally_B : nat -> trace -> Prop :=
| cofinally_B_nil: forall n st,
  st x = n -> B n -> cofinally_B n (Tcons st (Tnil st))
| cofinally_B_delay: forall n st tr,
  cofinally_B (S n) tr ->
  st x = n -> (B n -> False) -> cofinally_B n (Tcons st (Tcons st tr)).

Lemma cofinally_B_setoid: forall n tr0, cofinally_B n tr0 ->
 forall tr1, bisim tr0 tr1 -> cofinally_B n tr1.
Proof.
cofix CIH=> n tr0 h0 tr1 h1. inv h0.
- inv h1. inv H3.
  by apply: cofinally_B_nil.
- inv h1. inv H4.
  apply/cofinally_B_delay=>//. by apply/CIH/H5.
Qed.

Definition Cofinally_B (n: nat) : assertT.
exists (fun tr => cofinally_B n tr).
move=> tr0 /= h0 tr1 h1.
by apply/cofinally_B_setoid/h1.
Defined.

(* Lemma 5.2 *)
Lemma Cofinally_B_correct:
Cofinally_B 0 =>> (ttT *** [|B_holds_for_x|]).
Proof.
move => tr0 /= h0. exists tr0. split=>//.
suff: forall n tr, cofinally_B n tr ->
        follows (singleton B_holds_for_x) tr tr by apply; exact: h0.
cofix CIH=> n tr {}h0. inv h0.
- by apply/follows_delay/follows_nil/mk_singleton_nil.
- by apply/follows_delay/follows_delay/CIH/H.
Qed.

(* Lemma 5.1: cofinally_B 0 is stronger than nondivergent. *)
Lemma Cofinally_B_negInfinite : Cofinally_B 0 =>> negT Infinite.
Proof.
move => tr0 /= h0 h1.
have h2: forall n, exists tr : trace, (cofinally_B n tr) /\ (infinite tr).
* move => n. induction n.
  - by exists tr0.
  - move: IHn => [tr1 [h2 h3]].
    inv h2; first by inv h3; inv H1.
    inv h3. inv H2. by exists tr.
apply: B_noncontradictory => n. induction n=>h3.
- inv h0; first by inv h1; inv H2.
  by apply: H1.
- have [tr1 [h4 h5]] := h2 (S n).
  inv h4; first by inv h5; inv H2.
  by apply: H1.
Qed.

(*
 x := 0; while !(B x) (x := x + 1)
*)
Definition s : stmt := x <- (fun _ => 0);; Swhile cond (x <- incr_x).

(* Proposition 5.1 *)
Lemma Markov_search :
 semax ttS s ((ttT *** [|B_holds_for_x|]) andT negT Infinite).
Proof.
have hs0: semax ttS (x <- (fun _ => 0))
  ((Updt ttS x (fun _ => 0)) *** [| x_is_zero |]).
* apply/semax_conseq_R/semax_assign=> tr /= h0.
  exists tr. split => //.
  inv h0. destruct H as [_ h0]. inv h0. inv H1.
  apply/follows_delay/follows_nil/mk_singleton_nil=>//.
  by rewrite /update /x_is_zero Nat.eqb_refl.
have hs1: semax (x_is_zero)  (Swhile cond (x <- incr_x))
 ((ttT *** [|B_holds_for_x|]) andT negT Infinite).
pose u1 := ttS andS eval_true cond.
have h0 := semax_assign u1 x incr_x.
have h1 : (Updt u1 x incr_x) =>> ((Updt u1 x incr_x)  *** [|ttS|]).
* move => tr0 {}h0. exists tr0. split=>// {h0}.
  by exact: follows_ttS.
have h2 := semax_conseq_R h1 h0 => {h0 h1}.
have h0 : x_is_zero ->> ttS by [].
have h1 := semax_while h0 h2 => {h0 h2}.
have h0 :
  ((<< x_is_zero >>) *** Iter (Updt u1 x incr_x *** (<< ttS >>)) *** ([|eval_false cond|])) =>>
  Cofinally_B 0.
* move => tr0 [tr1 [[st0 [h0 h2]] {}h1]] /=.
  inv h2. inv H1. inv h1. inv H2.
  have h1: forall n st tr, hd tr x = n ->
    hd tr = st ->
    append (iter (append (updt u1 x incr_x) (dup ttS)))
    (singleton (eval_false cond)) tr ->
    cofinally_B n (Tcons st tr).
  * cofix CIH => {H1} n st0 tr0 h {}h0 [tr1 [h1 h2]]. inv h1.
    - inv h2. move: H1 => [st0 [h0 h1]]. inv h1. simpl.
      by apply/cofinally_B_nil/cond_false.
    - move: H => [tr2 [[st0 [h0 h3]] h1]].
      inv h3. inv H2. inv h1. inv H3. inv H0. inv h2.
      move: H2 => [st1 [h1 h2]]. inv h2. inv H2. simpl in H1.
      simpl. inv H5. inv H3. clear h1. inv H4.
      have h1: hd tr'1 = (update x (incr_x st0) st0).
      * rewrite -H0. by apply/esym/follows_hd/H5.
      have h2: hd tr'1 x = S (st0 x).
      * by rewrite h1 /update Nat.eqb_refl /incr_x; lia.
      have h3: (append (iter (append (updt u1 x incr_x) (dup ttS)))
        (singleton (eval_false cond))) tr'1.
        by exists tr'0.
      apply: (cofinally_B_delay (CIH _ _ _ h2 h1 h3)) => // {h1 h2 h3}.
      move: h0 => [_ h0]. apply: (cond_true h0).
    by apply: (h1 _ _ _ _ _ H1).
have h2 := semax_conseq_R h0 h1 => {h0 h1}.
have h0 := imp_andT Cofinally_B_correct Cofinally_B_negInfinite.
apply: (semax_conseq_R h0 h2) => {h2 h0}.
move: (semax_seq hs0 hs1) => {hs0 hs1}hs.
apply: (semax_conseq_R _ hs).
move => tr0 /= [tr1 [[st0 [h0 h2]] h1]].
inv h2. inv H1. clear h0. inv h1. inv H2. destruct H1 as [h0 h1]. split.
+ destruct h0 as [tr0 [_ h2]]. exists (Tcons st0 tr'). split => //.
  apply follows_delay.
  have h0 := follows_singleton h2.
  by apply: (follows_setoid (@singleton_setoid _) h2 h0 (bisim_reflexive _)).
move => h2. apply: h1. by inv h2.
Qed.
