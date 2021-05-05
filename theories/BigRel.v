From CoindSemWhile Require Import SsrExport Trace Language.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* big-step relational semantics *)
CoInductive exec: stmt -> state -> trace -> Prop :=
| exec_skip: forall st,
    exec Sskip st (Tnil st)
| exec_assign: forall id a st,
    exec (Sassign id a) st (Tcons st (Tnil (update id (a st) st)))
| exec_seq: forall s1 s2 st tr tr',
    exec s1 st tr ->
    execseq s2 tr tr' ->
    exec (Sseq s1 s2) st tr'
| exec_ifthenelse_true: forall a s1 s2 st tr,
    is_true (a st) ->
    execseq s1 (Tcons st (Tnil st)) tr ->
    exec (Sifthenelse a s1 s2) st tr
| exec_ifthenelse_false: forall a s1 s2 st tr,
    ~~ is_true (a st) ->
    execseq s2 (Tcons st (Tnil st)) tr ->
    exec (Sifthenelse a s1 s2) st tr
| exec_while_false: forall a s st,
    ~~ is_true (a st) ->
    exec (Swhile a s) st (Tcons st (Tnil st))
| exec_while_loop: forall a s st tr tr',
    is_true (a st) ->
    execseq s (Tcons st (Tnil st)) tr ->
    execseq (Swhile a s) tr tr' ->
    exec (Swhile a s) st tr'

with execseq: stmt -> trace -> trace -> Prop :=
| execseq_nil: forall st s tr,
  exec s st tr ->
  execseq s (Tnil st) tr
| execseq_cons: forall tr s tr' e,
  execseq s tr tr' ->
  execseq s (Tcons e tr) (Tcons e tr').

Lemma exec_nil: forall s st st',
exec s st (Tnil st') -> st = st'.
Proof.
elim.
- move=>?? h1.
  by inversion h1.
- move=>???? h1.
  by inversion h1.
- move=>? IHs1 ? IHs2 ?? h1; inv h1; inv H4.
  move: (IHs1 _ _ H1)=>->.
  by move: (IHs2 _ _ H)=>->.
- by move=>??????? h1; inv h1; inv H5; inv H5.
- by move=>????? h1; inv h1; inv H2; inv H5.
Qed.

Lemma execseq_deterministic0: forall s,
(forall st tr1 tr2, exec s st tr1 -> exec s st tr2 -> bisim tr1 tr2) ->
forall tr1 tr2 tr3 tr4,
bisim tr1 tr2 -> execseq s tr1 tr3 -> execseq s tr2 tr4 -> bisim tr3 tr4.
Proof.
move=>s hexec; cofix CIH=>tr1 tr2 tr3 tr4 h1 h2 h3; inv h2.
- inv h3.
  - by inv h1; apply/(hexec _ _ _ H).
  - by inversion h1.
- inv h3.
  - by inversion h1.
  - by inv h1; apply/bisim_cons/(CIH _ _ _ _ H2).
Qed.

Lemma exec_seq_deterministic0: forall s1 s2,
(forall st tr1 tr2, exec s1 st tr1 -> exec s1 st tr2 -> bisim tr1 tr2) ->
(forall st tr1 tr2, exec s2 st tr1 -> exec s2 st tr2 -> bisim tr1 tr2) ->
forall st tr1 tr2, exec (Sseq s1 s2) st tr1 ->
exec (Sseq s1 s2) st tr2 ->
bisim tr1 tr2.
Proof.
move=>s1 s2 hexec1 hexec2 st tr1 tr2 h1 h2.
inv h1; inv h2; have h3 := hexec1 _ _ _ H1 H2.
by apply: (execseq_deterministic0 hexec2 h3).
Qed.

Lemma exec_while_deterministic0: forall a s,
(forall st tr1 tr2, exec s st tr1 -> exec s st tr2 -> bisim tr1 tr2) ->
forall st tr1 tr2, exec (Swhile a s) st  tr1 ->
exec (Swhile a s) st tr2 ->
bisim tr1 tr2.
Proof.
move=>a s hwhile; cofix CIH.
have CIH2: forall tr1 tr2 tr3 tr4, bisim tr1 tr2 ->
execseq (Swhile a s) tr1 tr3 -> execseq (Swhile a s) tr2 tr4 ->
bisim tr3 tr4.
* cofix CIH2=> tr1 tr2 tr3 tr4 h1 h2 h3; inv h2.
  - inv h3.
    - inv h1; inv H0.
      - inv H.
        - by apply: bisim_reflexive.
        - by rewrite H2 in H5.
      - inv H.
        - by rewrite H3 in H6.
        - move=> {H3 H2}; inv H5; inv H3; inv H4; inv H5; inv H7; inv H9.
          by apply/bisim_cons/(CIH2 _ _ _ _ (hwhile _ _ _ H1 H2)).
    - by inversion h1.
  - inv h3.
    - by inversion h1.
    - by inv h1; apply/bisim_cons/(CIH2 _ _ _ _ H2).
* move=>st tr1 tr2 h1 h2; inv h1.
  - inv h2.
    - by apply: bisim_reflexive.
    - by rewrite H1 in H3.
  - inv h2.
    - by rewrite H1 in H6.
    - inv H2; inv H9; inv H4; inv H9; inv H5; inv H8.
      have h3 := hwhile _ _ _ H2 H4.
      by apply/bisim_cons/(CIH2 _ _ _ _ h3).
Qed.

(* determinism *)
Lemma exec_deterministic: forall s st,
forall tr1 tr2, exec s st tr1 ->
exec s st tr2 -> bisim tr1 tr2.
Proof.
move => s; induction s.
- move => st tr1 tr2 h1 h2. inv h1. inv h2. by apply bisim_nil.
- move => st tr1 tr2 h1 h2. inv h1. inv h2. by apply bisim_reflexive.
- move => st tr1 tr2 h1 h2. by apply: (exec_seq_deterministic0 IHs1 IHs2 h1 h2).
- move => st tr1 tr2 h1 h2. inv h1.
  - inv h2.
    - inv H5. inv H3. inv H7. inv H5. apply bisim_cons. apply: (IHs1 _ _ _ H1 H2).
    - by rewrite H4 in H6.
  - inv h2.
    - by rewrite H6 in H4.
    - inv H5. inv H3. inv H7. inv H4. inv H5. apply: (bisim_cons _ (IHs2 _ _ _ H1 H3)).
- move => st tr1 tr2 h1 h2. apply: (exec_while_deterministic0 IHs h1 h2).
Qed.

Lemma execseq_insensitive0: forall s,
(forall st tr1 tr2, exec s st tr1 -> bisim tr1 tr2 -> exec s st tr2) ->
forall tr1 tr2 tr3 tr4,
bisim tr1 tr2 ->
execseq s tr1 tr3 -> bisim tr3 tr4 -> execseq s tr2 tr4.
Proof.
move => s hexec0. cofix COINDHYP.
move => tr1 tr2 tr3 tr4 h1 h2 h3. inv h2. inv h1.
  by apply (execseq_nil (hexec0 _ _ _ H h3)).
- inv h3. inv h1. by apply: (execseq_cons _ (COINDHYP _ _ _ _ H4 H H3)).
Qed.

Lemma exec_seq_insensitive0: forall s1 s2,
(forall st tr1 tr2, exec s1 st tr1 -> bisim tr1 tr2 -> exec s1 st tr2) ->
(forall st tr1 tr2, exec s2 st tr1 -> bisim tr1 tr2 -> exec s2 st tr2) ->
forall st tr1 tr2, exec (Sseq s1 s2) st tr1 ->
bisim tr1 tr2 ->
exec (Sseq s1 s2) st tr2.
Proof.
move => s1 s2 hs1 hs2 st tr1 tr2 h1 h2. inv h1.
apply: (exec_seq H1). inv H4.
- by apply (execseq_nil (hs2 _ _ _ H h2)).
- inv h2. apply execseq_cons. have h2 := bisim_reflexive tr0.
  by apply: (execseq_insensitive0 hs2 h2 H H4).
Qed.

Lemma exec_while_insensitive0: forall a s,
(forall st tr1 tr2, exec s st tr1 -> bisim tr1 tr2 -> exec s st tr2) ->
forall st tr1 tr2, exec (Swhile a s) st tr1 ->
bisim tr1 tr2 ->
exec (Swhile a s) st tr2.
Proof.
move => a s hwhile. cofix COINDHYP.
have COINDHYP2: forall tr1 tr2 tr3 tr4, bisim tr1 tr2 ->
execseq (Swhile a s) tr1 tr3 -> bisim tr3 tr4 ->
execseq (Swhile a s) tr2 tr4.
* cofix COINDHYP2. move => tr1 tr2 tr3 tr4 h1 h2 h3. inv h2.
  - inv h1. by apply: (execseq_nil (COINDHYP _ _ _ H h3)).
  - inv h1. inv h3. by apply: (execseq_cons _ (COINDHYP2 _ _ _ _ H3 H H4)).
- move => st tr1 tr2 h1 h2. inv h1.
  - inv h2. inv H2. by apply: (exec_while_false _ H3).
  - inv H2. inv H6. inv H5. inv h2.
    apply: (exec_while_loop H1 (execseq_cons _ (execseq_nil H2))).
    by apply: (execseq_cons _ (COINDHYP2 _ _ _ _ (bisim_reflexive tr') H6 H4)).
Qed.

(* setoid *)
Lemma exec_insensitive: forall s st tr tr',
exec s st tr -> bisim tr tr' -> exec s st tr'.
Proof.
move => s; induction s.
- move => st tr tr' h1 h2. inv h1. inv h2. by apply exec_skip.
- move => st tr tr' h1 h2. inv h1. inv h2. inv H2. by apply exec_assign.
- move => st tr tr' h1 h2. apply: (exec_seq_insensitive0 IHs1 IHs2 h1 h2).
- move => st tr tr' h1 h2. inv h1.
  - inv H5. inv H3. inv h2. apply: (exec_ifthenelse_true _ H4).
    apply execseq_cons. apply execseq_nil. by apply: (IHs1 _ _ _ H1 H3).
  - inv H5. inv H3. inv h2. apply: (exec_ifthenelse_false _ H4).
    apply execseq_cons. apply execseq_nil. by apply: (IHs2 _ _ _ H1 H3).
- move => st tr tr7 h1 h2. by apply: (exec_while_insensitive0 IHs h1 h2).
Qed.

Lemma execseq_insensitive_pre: forall s tr1 tr2 tr3,
bisim tr1 tr2 -> execseq s tr1 tr3 -> execseq s tr2 tr3.
Proof.
cofix COINDHYP. move => s tr1 tr2 tr3 h1 h2. inv h2; inv h1.
- by apply: (execseq_nil H).
- apply: execseq_cons. by apply: (COINDHYP _ _ _ _ H3 H).
Qed.

Lemma exec_hd: forall s st tr,
exec s st tr -> hd tr = st.
Proof.
move => s; induction s.
- move => st tr h1. by inv h1.
- move => st tr h1. by inv h1.
- move => st tr h1. inv h1.
  have h1 := IHs1 _ _ H1. inv H4=>//=. by apply: (IHs2 _ _ H).
- move => st tr h1. inv h1.
  - by inv H5.
  - by inv H5.
- move => st tr h1. inv h1=>//=.
  inv H2. inv H6. by inv H5.
Qed.

Lemma execseq_hd: forall s tr tr',
execseq s tr tr' -> hd tr' = hd tr.
Proof.
move => s tr tr' h1. inv h1=>//=.
by apply: (exec_hd H).
Qed.
