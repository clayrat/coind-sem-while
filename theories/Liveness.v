From CoindSemWhile Require Import SsrExport Trace Language Assert Semax.
From Coq Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable x : id.
Variable tt : expr.
Axiom tt_true : forall st, is_true (tt st).

Definition incr_x : expr := fun st => st x + 1.
Definition x_is_zero : assertS := fun st => st x = 0.

Lemma update_x_incr_x : forall st,
 update x (incr_x st) st x = st x + 1.
Proof. by rewrite /update Nat.eqb_refl. Qed.

Inductive eventually_x_is_n (n: nat) : trace -> Prop :=
| x_is_n_nil: forall st, st x = n -> eventually_x_is_n n (Tnil st)
| x_is_n_cons: forall st tr, st x = n -> eventually_x_is_n n (Tcons st tr)
| x_is_n_delay: forall st tr,
  eventually_x_is_n n tr -> eventually_x_is_n n (Tcons st tr).

Lemma eventually_x_is_n_setoid: forall n tr,
 eventually_x_is_n n tr -> forall tr0, bisim tr tr0 ->
 eventually_x_is_n n tr0.
Proof.
induction 1=> tr0 h0; inv h0.
- by apply: x_is_n_nil.
- by apply: x_is_n_cons.
- by apply/x_is_n_delay/IHeventually_x_is_n.
Qed.

Definition Eventually_x_is_n (n:nat): assertT.
exists (eventually_x_is_n n).
move => tr0 h0 tr1 h1. by exact: (eventually_x_is_n_setoid h0 h1).
Defined.

(*
x := 0; while true (x := x + 1)
*)
Definition s : stmt := x <- (fun _ => 0);; Swhile tt (x <- incr_x).

(* Proposition 5.2 *)
Lemma prg_spec: forall (n: nat), semax ttS s (Eventually_x_is_n n).
Proof.
move => n.
have hs0: semax ttS (x <- (fun _ => 0))
            (Updt ttS x (fun _ => 0) *** [| x_is_zero |]).
* apply/semax_conseq_R/semax_assign=> tr /= h0.
  exists tr. split => //.
  inv h0. destruct H as [_ h0]. inv h0. inv H1.
  apply/follows_delay/follows_nil/mk_singleton_nil => //.
  by rewrite /update /x_is_zero Nat.eqb_refl.
have hs1 : semax x_is_zero (Swhile tt (x <- incr_x)) (Eventually_x_is_n n).
have h0 := semax_assign ttS x incr_x.
have h1 : (ttS andS eval_true tt) ->> ttS by [].
have h2 : (Updt ttS x incr_x) =>> (Updt ttS x incr_x) *** [| ttS |].
* move => tr0 {h1}h0. exists tr0. split => // {h0}.
  by exact: follows_ttS.
have h3 := semax_conseq h1 h2 h0 => {h0 h1 h2}.
have h0 : x_is_zero ->> ttS by [].
have h1 := semax_while h0 h3 => {h0 h3}.
have h0 : ((<< x_is_zero >>) ***
 Iter (Updt ttS x incr_x *** (<< ttS >>)) *** ([|eval_false tt|])) =>>
 (Eventually_x_is_n n).
* move => tr0 [tr1 [[st0 [h0 h2]] {}h1]].
  inv h2. inv H1. inv h1. inv H2. simpl.
  have h1: forall n tr,
   append (iter (append (updt ttS x incr_x) (dup ttS)))
       (singleton (eval_false tt)) tr ->
   eventually_x_is_n (hd tr x + n) tr.
  * move => {H1 h0 tr'}n. induction n.
    - case=> st0.
      + move =>_. apply: x_is_n_nil=>/=; by lia.
      move => tr0 _. apply: x_is_n_cons=>/=; by lia.
    - move => tr0 [tr1 [h0 h1]]. inv h0.
      + inv h1. move: H1 => [st0 [h0 _]]. by rewrite /eval_false tt_true in h0.
      move: H => [tr2 [[st0 [_ h0]] h2]].
      inv h0. inv H2. inv h2. inv H0. inv H3.
      move: H1 => [st1 [_ h2]]. inv h2. simpl in H0.
      inv H2. inv h1. inv H4. inv H3. inv H2. simpl.
      apply x_is_n_delay.
      have h0 := follows_singleton H5.
      have h1: append (iter (append (updt ttS x incr_x) (dup ttS)))
       (singleton (eval_false tt)) tr'1.
      + exists tr'1; split=>//.
        by apply: (follows_setoid_R (@singleton_setoid _) H5 (bisim_symmetric h0)).
      have h2 := IHn _ h1 => {h1 H5}.
      have h1: st0 x + S n = hd tr'1 x + n
        by rewrite H0 (update_x_incr_x st0); lia.
      rewrite h1 => {h1}. apply x_is_n_delay.
      by apply: (eventually_x_is_n_setoid h2 h0).
  apply x_is_n_delay.
  have h2 := h1 _ _ H1 => {h1 H1}.
  inv h0.
  have h0: n = hd tr' x + n by rewrite H0; lia.
  rewrite {}h0.
  by apply h2.
by apply: (semax_conseq_R h0 h1).
move: (semax_seq hs0 hs1) => {hs0 hs1}hs.
apply: (semax_conseq_R _ hs) => {hs} tr0 /= [tr1 [[st0 [h0 h2]] h1]].
inv h2. inv H1. inv h1. inv H2. by apply x_is_n_delay.
Qed.
