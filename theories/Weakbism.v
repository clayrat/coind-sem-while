From CoindSemWhile Require Import SsrExport Trace Language Semax.
From CoindSemWhile Require Import Assert AssertClassical.
From Coq Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable x : id.
Variable y : id.
Axiom xy : x =? y = false.
Variable cond : expr. (* y <> 0 *)
Axiom cond_true: forall st, eval_true cond st -> (st y <> 0).
Variable tt : expr.
Axiom tt_true: forall st, is_true (tt st) = true.

Lemma yx : y =? x = false.
Proof. by rewrite Nat.eqb_sym; apply xy. Qed.

Definition incr_x: expr := fun st => st x + 1.
Definition decr_y: expr := fun st => st y - 1.

Inductive red_hd_x : trace -> trace -> Prop :=
| red_hd_x_stop: forall st tr tr',
  st x <> hd tr x ->
  bisim tr tr' ->
  red_hd_x (Tcons st tr) tr'
| red_hd_x_tau: forall st tr tr',
  st x = hd tr x ->
  red_hd_x tr tr' ->
  red_hd_x (Tcons st tr) tr'.

Lemma red_hd_x_deterministic: forall tr0 tr1, red_hd_x tr0 tr1 ->
forall tr2, red_hd_x tr0 tr2 -> bisim tr1 tr2.
Proof.
induction 1=> tr0 h0; inv h0=>//.
- by apply: (bisim_transitive (bisim_symmetric H0) H5).
- by apply: (IHred_hd_x _ H5).
Qed.

Lemma red_hd_x_setoid: forall tr0 tr1, red_hd_x tr0 tr1 ->
forall tr2, bisim tr0 tr2 -> forall tr3, bisim tr1 tr3 -> red_hd_x tr2 tr3.
Proof.
induction 1.
- move => tr0 h0 tr1 h2. inv h0.
  rewrite (bisim_hd H4) in H.
  by apply: (red_hd_x_stop H (bisim_transitive (bisim_transitive (bisim_symmetric H4) H0) h2)).
- move => tr0 h0 tr1 h1. inv h0.
  rewrite (bisim_hd H4) in H.
  apply: (red_hd_x_tau H). by apply: (IHred_hd_x _ H4 _ h1).
Qed.

CoInductive up : nat -> trace -> Prop :=
| up_intro: forall st n tr0 tr1,
  st x = n ->
  red_hd_x (Tcons st tr0) tr1 -> up (S n) tr1 ->
  up n (Tcons st tr0).

Lemma up_setoid: forall n tr0, up n tr0 ->
forall tr1, bisim tr0 tr1 -> up n tr1.
Proof.
move => n tr0 h0 tr1 h1. inv h0. inv h1.
have h1 := red_hd_x_setoid H0 (bisim_cons st H4) (bisim_reflexive tr3).
by apply: (up_intro (refl_equal (st x)) h1 H1).
Qed.

Definition Up (n:nat): assertT.
exists (fun tr => up n tr).
move => tr0 h0 tr1 h1.
by apply: (up_setoid h0 h1).
Defined.

Inductive skips: trace -> Prop :=
| skips_nil: forall st, skips (Tnil st)
| skips_delay: forall st tr,
  skips tr -> hd tr x = st x -> skips (Tcons st tr).

Lemma skips_setoid: forall tr0, skips tr0 -> forall tr1, bisim tr0 tr1 ->
skips tr1.
Proof.
induction 1.
- move => st0 h0. inv h0. by apply skips_nil.
- move => tr0 h0. inv h0. apply skips_delay.
  - by apply: (IHskips _ H4).
  by rewrite -(bisim_hd H4).
Qed.

Definition Skips: assertT.
exists (fun tr => skips tr).
move => tr0 h0 tr1 h1 /=.
by apply: (skips_setoid h0 h1).
Defined.

Lemma Sn_1 : forall n, S n - 1 = n.
Proof. by move => n; lia. Qed.

Lemma Sn: forall n, n + 1 = S n.
Proof. by move => n; lia. Qed.

Definition x_is_zero : assertS := fun st => st x = 0.

(*
while true
 (y := x;
  while y != 0 (y := y - 1);
  x := x + 1)
*)

Definition s : stmt :=
 Swhile tt
  (y <- (fun st => st x);;
   Swhile cond (y <- decr_y);;
   x <- incr_x).

(* Proposition 5.3 *)
Lemma spec: semax x_is_zero s (Up 0).
Proof.
rewrite /s.
pose a_t := eval_true cond.
pose a_f := eval_false cond.
pose u_xy := fun st: state => st x = st y.
have h0 := semax_assign (ttS andS a_t) y decr_y.
have h1 := semax_conseq_R (@Append_ttS _) h0 => {h0}.
have h0: ttS ->> ttS by [].
have h2 := semax_while h0 h1 => {h0 h1}.
have h0 : ((<< ttS >>) *** Iter (Updt (ttS andS a_t) y decr_y *** (<< ttS >>)) ***
 [|eval_false cond|]) =>> Skips.
* move => {h2} tr0 /= h0. move h1: (hd tr0 y) => n.
  move: tr0 h1 h0. induction n.
  - move => tr0 h0 [tr1 [[st0 [_ h1]] h2]].
    inv h1. inv H1. inv h2. simpl in h0. inv H2. move: H1 => [tr0 [h1 h2]]. inv h1.
    - inv h2. move: H1 => [st0 [_ h1]]. inv h1. simpl.
      apply skips_delay=>//. by apply skips_nil.
    - move: H => [tr1 [h1 h3]]. move: h1 => [st0 [[_ h1] h4]].
      inv h4. inv h3. inv H0. inv h2. simpl in h0.
      by move: (cond_true h1 h0).
  - move => tr0 h0 [tr1 [[st0 [_ h3]] h2]].
    inv h3. inv H1. inv h2. simpl in h0. inv H2. apply skips_delay=>//.
    move: H1 => [tr0 [h1 h2]]. inv h1.
    - inv h2. move: H1 => [st0 [h1 h2]]. inv h2. by apply: skips_nil.
    - move: H => [tr1 [h1 h3]]. move: h1 => [st0 [h1 h4]].
      inv h4. inv H2. inv h3. inv H0. inv H3. inv h2. simpl in h0.
      have h2: skips tr'1.
      - apply: IHn.
        - have h2 := follows_hd H4.
          rewrite -{}h2 {}H0 /decr_y {}h0 /update Nat.eqb_refl.
          by apply Sn_1.
        exists tr'0. split=>//.
        move: H1 => [st1 [_ h2]]. inv h2. simpl in H0. inv H2. inv H4.
        apply follows_delay. inv H2. inv H5. apply follows_nil => //.
        exists tr'. split=>//.
        have h2 := follows_singleton H4.
        by apply: (follows_setoid_R (@singleton_setoid _) H4 (bisim_symmetric h2)).
      apply skips_delay.
      have h3 := follows_singleton H5.
      apply: (skips_setoid h2 h3).
      have h3 := follows_hd H5.
      rewrite -{}h3 => {h2 h0 H1 H5}.
      have h0 := follows_hd H4 => {H4}.
      by rewrite -{}h0 {}H0 /update yx.
have h1 := semax_conseq_R h0 h2 => {h0 h2}.
have h0 := semax_assign ttS x incr_x.
have h2 := semax_conseq_R (@Append_ttS _) h1 => {h1}.
have h1 := semax_seq h2 h0 =>  {h2 h0}.
have h0 := semax_conseq_R (@Append_ttS _) (semax_assign ttS y (fun st => st x)).
have h2 := semax_seq h0 h1 => {h0 h1}.
have h0 := semax_conseq_R (@Append_assoc_R _ _ _) h2 => {h2}.
have h1: (Updt ttS y (fun st => st x) *** Skips) =>> Skips.
* move => tr0 [tr1 [[st0 [_ {}h0]] h1]] /=.
  inv h0. inv H1. inv h1. inv H2. apply skips_delay => //.
  by rewrite H0 /update yx.
have h2 := semax_conseq_R (Append_monotone_L h1) h0 => {h0 h1}.
have h0: x_is_zero ->> ttS by [].
have h1: (ttS andS eval_true tt) ->> ttS by [].
have h3 := semax_conseq h1 (@Append_ttS _) h2 => {h2 h1}.
have h1 := semax_while h0 h3 => {h0 h3}.
have h0: (<<x_is_zero>> *** Iter ((Skips *** Updt ttS x incr_x)
*** <<ttS>>) *** [| eval_false tt |]) =>> (Up 0).
* move => {h1} tr0 /= [tr1 [[st0 [h0 h2]] h1]]. rewrite /x_is_zero in h0.
  inv h2. inv H1. inv h1. inv H2. move: H1 => [tr0 [h1 h2]].
  have: forall n tr0 tr1, hd tr1 x = n ->
   iter (append (append (fun tr => skips tr) (updt ttS x incr_x)) (dup ttS)) tr0 ->
   follows (singleton (eval_false tt)) tr0 tr1 -> up n (Tcons (hd tr1) tr1).
  * cofix CIH=> {tr'} n {}tr0 tr1 {}h0 {}h1 {}h2. inv h1.
    - inv h2. move: H1 => [st0 [h0 h1]]. rewrite /eval_false in h0. clear h1.
      by rewrite tt_true in h0.
    - move: H => [tr2 [[tr3 [h0 h3]] h1]].
      have h4: forall tr3, skips tr3 ->
      forall tr2, follows (updt ttS x incr_x) tr3 tr2 ->
      forall tr, follows (dup ttS) tr2 tr ->
      forall tr0, follows (iter
          (append (append (fun tr : trace => skips tr)
           (updt ttS x incr_x)) (dup ttS))) tr tr0 ->
      forall tr1, follows (singleton (eval_false tt)) tr0 tr1 ->
      exists tr4 : trace, ((red_hd_x (Tcons (hd tr1) tr1) (Tcons (hd tr4) tr4)) /\
        (hd tr4 x = S (hd tr1 x)) /\
        (iter (append
         (append (fun tr : trace => skips tr)
         (updt ttS x incr_x)) (dup ttS)) tr4) /\
         (follows (singleton (eval_false tt)) tr4 tr4)).
       * clear CIH tr0 tr1 h2 tr H0 tr2 h1 tr3 h0 h3. induction 1.
          - move => tr0 h0 tr1 h1 tr2 h2 tr3 h3. inv h0.
            move: H1 => [st0 [h0 h4]]. inv h4. inv h1. inv H1. clear h0.
            inv H3. inv h2. move: H1 => [st1 [h0 h1]]. inv h1. inv H2.
            simpl in H0. inv H4. clear h0. inv H3. inv h3. inv H4. exists tr'.
            have h0 := follows_hd H5.
            have h1 := follows_singleton H5.
            split.
            - apply red_hd_x_tau=>//. apply red_hd_x_stop.
              - rewrite /= /update Nat.eqb_refl /incr_x. by lia.
              rewrite H0.
              by apply/bisim_cons/bisim_symmetric.
            rewrite /= H0 /update Nat.eqb_refl. split; first by apply Sn.
            split; first by apply H1.
            apply: (follows_setoid _ H5 _ (bisim_symmetric h1)).
            - move => tr0 h2 tr1 h3. move: h2 => [st1 [h2 h4]]. inv h4.
              exists st1. split => //. by apply: (bisim_symmetric h3).
            by apply bisim_reflexive.
          - move => tr0 h0 tr1 h1 tr2 h2 tr3 h3. inv h0.
            have h0 := IHskips _ H4 => {IHskips}. inv h1.
            have h1 := h0 _ H5 => {h0}. inv h2.
            have h2 := h1 _ H6 => {h1}. inv h3.
            have [tr0 [h3 [h0 [h1 {}h2]]]] := h2 _ H7.
            rewrite /= -H0.
            have h4 := follows_hd H4; rewrite h4 => {H4}.
            have h5 := follows_hd H5; rewrite h5 => {H5}.
            have h6 := follows_hd H6; rewrite h6 => {H6}.
            have h7 := follows_hd H7; rewrite h7 => {H7}.
            rewrite -h0.
            exists tr0. split => // {h1 h2}.
            apply red_hd_x_tau=>//.
            inv h3; first by absurd False=>//; apply: H3.
            apply red_hd_x_tau; first by rewrite -H0 h4 h5 h6 h7.
            by apply H5.
     have [tr4 [{}h4 [h7 [h5 h6]]]]:= h4 _ h0 _ h3 _ h1 _ H0 _ h2 => {h0 h3 h1 H0 h2}.
     apply: (up_intro _ h4)=>//.
     apply: (CIH _ _ _ _ _ h6); first by apply: h7.
     by apply h5.
  move => h3. by apply: (h3 _ _ _ h0 h1 h2).
by apply: (semax_conseq_R h0 h1).
Qed.
