Require Import Bool Arith List Omega.
Require Import Recdef Morphisms.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require FMapList.
Require FMapFacts.
Require Import Classical.
Require Import Coq.Classes.RelationClasses.
Require Import OrderedType OrderedTypeEx DecidableType.
Require Import Sorting.Permutation.
Import ListNotations.
Module NatMap := FMapList.Make Nat_as_OT.

Definition address := nat.
Definition version := nat.
Definition value := nat.
Definition lock := bool.
Definition variable := nat.
Definition store := NatMap.t value.
Definition heap :=  address -> option (value * lock * version).
Definition tid := nat.


Ltac myauto :=
  repeat match goal with
  | |- context[_] =>
      auto 100; intuition; cbn in *; simpl in *; auto 100
  | |- context[_] =>
      try contradiction; try discriminate
end.


Inductive action:=
|dummy: action
|start_txn: action
|read_item: version -> action
|write_item: value -> action
|try_commit_txn: action
|lock_write_item: action
|seq_point: action
|validate_read_item: version -> action
|abort_txn: action
|unlock_write_item: action
(*|restart_txn: action*)
|commit_txn: action
|complete_write_item: (*value -> action*)version -> action
(*|unlock_write_item: version -> action*)
(*|invalid_write_item: value -> action*)
|commit_done_txn: action.
(*|obtain_global_tid: action.*)
(*sp later than last lock, but must before the first commit*)
Definition trace := list (tid * action).

(* Return the “phase” of an action. *)
Definition action_phase (a:action) :=
  match a with
  | dummy => 0
  | start_txn => 1
  | read_item _ => 1
  | write_item _ => 1
  | try_commit_txn => 2
  | lock_write_item => 2
  | seq_point => 3
  | validate_read_item _ => 3
  | commit_txn => 4
  | complete_write_item _ => 4
  | commit_done_txn => 4
  | abort_txn => 6
  | unlock_write_item => 6
  end.

Fixpoint trace_tid_phase tid t: nat :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then action_phase a
    else trace_tid_phase tid t'
  | [] => 0
  end.

(* Return the version number of the last committed write *)
Fixpoint trace_write_version (t:trace): version :=
  match t with
  | (_, complete_write_item v) :: _ => v
  | _ :: t' => trace_write_version t'
  | [] => 0
  end.

Fixpoint trace_tid_last_write tid t: option value :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then match a with
         | write_item v => Some v
         | complete_write_item _ => None
         | _ => trace_tid_last_write tid t'
         end
    else trace_tid_last_write tid t'
  | [] => None
  end.

Fixpoint trace_validate_read tid vers aborted (t:trace) :=
  match t with
  | (tid', lock_write_item) :: t' =>
    (tid = tid' \/ aborted) /\ trace_validate_read tid vers False t'
  | (_, unlock_write_item) :: t' =>
    trace_validate_read tid vers True t'
  | (_, complete_write_item vers') :: _ => vers = vers'
  | _ :: t' => trace_validate_read tid vers aborted t'
  | [] => vers = 0
  end.

Fixpoint locked_by (t:trace) default : tid :=
  match t with
  | (tid, lock_write_item) :: _ => tid
  | (_, unlock_write_item) :: _ => default
  | (_, complete_write_item _) :: _ => default
  | _ :: t' => locked_by t' default
  | [] => default
  end.

Inductive sto_trace : trace -> Prop :=

| empty_step : sto_trace []

| start_txn_step: forall t tid,
    tid > 0
    -> trace_tid_phase tid t = 0
    -> sto_trace t
    -> sto_trace ((tid, start_txn)::t)

| read_item_step: forall t tid,
    trace_tid_phase tid t = 1
    -> locked_by t 0 = 0
    -> sto_trace t
    -> sto_trace ((tid, read_item (trace_write_version t)) :: t)

| write_item_step: forall t tid val,
    trace_tid_phase tid t = 1
    -> sto_trace t
    -> sto_trace ((tid, write_item val) :: t)

| try_commit_txn_step: forall t tid,
    trace_tid_phase tid t = 1
    -> sto_trace t
    -> sto_trace ((tid, try_commit_txn)::t)

| lock_write_item_step: forall t tid v,
    trace_tid_phase tid t = 2
    -> In (tid, write_item v) t
    -> locked_by t 0 = 0
    -> sto_trace t
    -> sto_trace ((tid, lock_write_item) :: t)

(*sequential point*)
| seq_point_step: forall t tid,
    trace_tid_phase tid t = 2
    -> (forall v, In (tid, write_item v) t
                  -> In (tid, lock_write_item) t)
    -> sto_trace t
    -> sto_trace ((tid, seq_point) :: t)

| validate_read_item_step: forall t tid vers,
    trace_tid_phase tid t = 3
    -> locked_by t tid = tid (* unlocked or locked by me *)
    -> trace_write_version t = vers
    -> sto_trace t
    -> sto_trace ((tid, validate_read_item vers) :: t)

| abort_txn_step: forall t tid,
    trace_tid_phase tid t > 0
    -> trace_tid_phase tid t < 4
    -> sto_trace t
    -> sto_trace ((tid, abort_txn) :: t)

| unlock_item_step: forall t tid,
    trace_tid_phase tid t = 6
    -> locked_by t 0 = tid
    -> sto_trace t
    -> sto_trace ((tid, unlock_write_item) :: t)

| commit_txn_step: forall t tid,
    trace_tid_phase tid t = 3
    -> (forall vers, In (tid, read_item vers) t
                     -> In (tid, validate_read_item vers) t)
    -> sto_trace t
    -> sto_trace ((tid, commit_txn) :: t)

| complete_write_item_step: forall t tid val,
    trace_tid_phase tid t = 4
    -> locked_by t 0 = tid
    -> trace_tid_last_write tid t = Some val
    -> sto_trace t
    -> sto_trace ((tid, complete_write_item (S (trace_write_version t))) :: t)

| commit_done_step: forall t tid,
    trace_tid_phase tid t = 4
    -> locked_by t 0 <> tid
    -> sto_trace t
    -> sto_trace ((tid, commit_done_txn) :: t).
Hint Constructors sto_trace.


Definition example_txn:=
[(2, commit_done_txn); (2, complete_write_item 1); (2, commit_txn); (2, validate_read_item 0); (2, seq_point); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (2, read_item 0); (2, start_txn); (1, commit_done_txn); (1, commit_txn); (1, validate_read_item 0); (1, seq_point); (1, try_commit_txn); (1, read_item 0); (1, start_txn)].

Definition example_txn2:=
[(3, commit_done_txn); (3, commit_txn); (3, validate_read_item 1); (3, seq_point); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item 1); (1, try_commit_txn); (2, commit_txn); (2, complete_write_item 1); (2, commit_txn); (2, validate_read_item 0); (2, seq_point); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)].

Lemma sto_trace_cons ta t:
  sto_trace (ta :: t) -> sto_trace t.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma sto_trace_app t1 t2:
  sto_trace (t1 ++ t2) -> sto_trace t2.
Proof.
  intros.
  induction t1. rewrite app_nil_l in H. auto.
  apply IHt1.
  now apply sto_trace_cons with (ta:=a).
Qed.

(*
Returns the serialized sequence of transactions in the STO trace based on seq_point of each transaction
The first element (tid) of the sequence is the first transaction that completes in the serial trace
Note that STO-trace is constructed in a reverse order: the first (tid * action) pair is the last operation in the trace
*)

Function seq_list (sto_trace: trace): list nat:=
  match sto_trace with
  | [] => []
  | (tid, seq_point) :: tail => seq_list tail ++ [tid]
  | _ :: tail => seq_list tail
  end.

Eval compute in seq_list example_txn.

Eval compute in seq_list example_txn2.

Lemma phase_increase_head tid a t:
  sto_trace ((tid, a) :: t) ->
  action_phase a >= trace_tid_phase tid t.
Proof.
  intros; inversion H; cbn; omega.
Qed.

Lemma phase_increase_app tid t1 t2:
  sto_trace (t1 ++ t2) ->
  trace_tid_phase tid (t1 ++ t2) >= trace_tid_phase tid t2.
Proof.
  induction t1; intros.
  - simpl; omega.
  - rewrite <- app_comm_cons in H; destruct a.
    assert (sto_trace (t1 ++ t2)) by (now apply sto_trace_cons in H).
    apply IHt1 in H0.
    simpl; destruct (Nat.eq_dec tid t).
    + subst; apply phase_increase_head in H; omega.
    + auto.
Qed.

Lemma phase_increase_in tid a t:
  sto_trace t ->
  In (tid, a) t ->
  trace_tid_phase tid t >= action_phase a.
Proof.
  intros H I; apply in_split in I.
  destruct I as [l1 [l2 L]].
  assert (trace_tid_phase tid ((tid, a) :: l2) = action_phase a). {
    cbn; destruct (Nat.eq_dec tid tid); omega.
  }
  rewrite L in *; rewrite <- H0; now apply phase_increase_app.
Qed.

Lemma phase_increase_in_app tid a (t1 t2:trace):
  sto_trace (t1 ++ t2) ->
  In (tid, a) (t1 ++ t2) ->
  action_phase a > trace_tid_phase tid t2 ->
  In (tid, a) t1.
Proof.
  intros T I A.
  apply in_app_or in I; destruct I as [I | I]; auto.
  apply sto_trace_app in T.
  apply (phase_increase_in _ _ _ T) in I.
  omega.
Qed.
  
Lemma at_most_one_seq_point tid t:
  sto_trace ((tid, seq_point) :: t) ->
  ~ In (tid, seq_point) t.
Proof.
  intros H F.
  apply (phase_increase_in _ _ _ (sto_trace_cons _ _ H)) in F.
  inversion H; subst; cbn in *.
  omega.
Qed.

Lemma trace_phase_in tid t:
  trace_tid_phase tid t > 0 ->
  exists a, In (tid, a) t.
Proof.
  induction t; intros; cbn in *.
  omega.
  destruct a.
  destruct (Nat.eq_dec tid n).
  exists a; subst; now left.
  apply IHt in H; destruct H as [a' H]; exists a'; now right.
Qed.

Lemma tid_nonzero tid a t:
  sto_trace t ->
  In (tid, a) t ->
  tid > 0.
Proof.
  revert tid a; induction t.
  - intros tid a H I; destruct I.
  - intros tid' a' H I.
    destruct I; [ | now apply (IHt _ _ (sto_trace_cons _ _ H)) in H0 ].
    subst; inversion H; auto.
    all: assert (trace_tid_phase tid' t > 0) as GZ by omega.
    all: apply trace_phase_in in GZ.
    all: destruct GZ as [a GZ].
    all: now apply (IHt tid' a).
Qed.

Lemma trace_phase_nonzero tid t:
  sto_trace t ->
  trace_tid_phase tid t > 0 ->
  tid > 0.
Proof.
  intros T; induction T; intros P; simpl in P.
  omega.
  all: destruct (Nat.eq_dec tid tid0); [subst; auto | now apply IHT].
  all: try solve [apply IHT; omega].
Qed.

Lemma track_lock_cons tid tid' t a:
  sto_trace ((tid', a) :: t) ->
  locked_by t 0 = tid ->
  locked_by ((tid', a) :: t) 0 = tid
  \/ tid = 0 /\ a = lock_write_item
  \/ tid = tid' /\ a = unlock_write_item
  \/ tid = tid' /\ exists val, a = complete_write_item val.
Proof.
  intros T L.
  assert (tid' > 0) as TG. {
    apply tid_nonzero with (a:=a) (t:=(tid', a)::t); cbn; auto.
  }
  inversion T; subst; cbn; auto.
  right; right; right; eauto.
Qed.

Lemma locked_phase tid t:
  sto_trace t ->
  locked_by t 0 = tid ->
  tid > 0 ->
  trace_tid_phase tid t >= 2.
Proof.
  intros T; revert tid; induction T; intros tid L G.
  1: cbn in L; omega.
  all: cbn.
  all: destruct (Nat.eq_dec tid tid0); try omega.
  all: try (now apply IHT).
  1-3: subst; apply IHT in e; omega.
  1-3: simpl in L; omega.
Qed.

Lemma commit_phase_cons tid p t:
  sto_trace (p :: t) ->
  trace_tid_phase tid t = 4 ->
  trace_tid_phase tid (p :: t) = 4.
Proof.
  destruct p as [tid' a]; intros T Fo; inversion T; cbn in *.
  all: destruct (Nat.eq_dec tid tid'); auto.
  all: subst; omega.
Qed.

Lemma commit_phase_app tid t1 t2:
  sto_trace (t1 ++ t2) ->
  trace_tid_phase tid t2 = 4 ->
  trace_tid_phase tid (t1 ++ t2) = 4.
Proof.
  induction t1; intros.
  now simpl.
  rewrite <- app_comm_cons in *.
  apply commit_phase_cons; auto.
  apply IHt1; auto.
  now apply sto_trace_cons in H.
Qed.


Lemma phase_2_preserves_lock tid t1 t2:
  sto_trace (t1 ++ t2) ->
  trace_tid_phase tid (t1 ++ t2) = 2 ->
  locked_by t2 0 = tid ->
  locked_by (t1 ++ t2) 0 = tid.
Proof.
  revert t2.
  induction t1; intros t2 T P L.
  now cbn.
  destruct a as [tid' a].
  cbn in P; destruct (Nat.eq_dec tid tid').
  - destruct a; simpl in *; try omega.
    + rewrite e in *; clear e tid.
      assert (trace_tid_phase tid' t2 >= 2). {
        apply locked_phase.
        now apply sto_trace_app with (t1:=(tid',try_commit_txn)::t1).
        auto.
        apply tid_nonzero with (a:=try_commit_txn) (t:=(tid', try_commit_txn)::t1 ++ t2).
        auto.
        simpl; now left.
      }
      inversion T; subst.
      apply (phase_increase_app (locked_by t2 0)) in H3; omega.
    + auto.
  - assert (locked_by (t1 ++ t2) 0 = tid) as LA. {
      apply IHt1; auto.
      now apply (sto_trace_cons _ _ T).
    }
    clear IHt1 L.

    assert (tid > 0). {
      apply trace_phase_nonzero with (t:=t1++t2).
      now apply sto_trace_cons with (ta:=(tid',a)).
      omega.
    }

    inversion T; cbn in *; auto; omega.
Qed.

Lemma locked_at_commit tid t1 t2 v:
  sto_trace ((tid, seq_point) :: t1 ++ (tid, write_item v) :: t2) ->
  locked_by (t1 ++ (tid, write_item v) :: t2) 0 = tid.
Proof.
  intros T.
  inversion T.
  assert (tid > 0) as TG. {
    apply tid_nonzero with (a:=write_item v) (t:=t); rewrite H0; auto.
    apply in_or_app; right; now left.
  }

  assert (In (tid, lock_write_item) t1). {
    assert (In (tid, lock_write_item) t). {
      rewrite H0.
      apply H2 with (v0:=v).
      apply in_or_app; cbn; intuition.
    }
    apply phase_increase_in_app with (t2:=(tid, write_item v) :: t2); auto.
    now rewrite <- H0.
    simpl; destruct (Nat.eq_dec tid tid); intuition.
  }

  apply in_split in H4.
  destruct H4 as [t1a [t1b T1]].
  subst.
  repeat rewrite <- app_assoc in *.
  repeat rewrite <- app_comm_cons in *.
  remember ((tid, lock_write_item) :: t1b ++ (tid, write_item v) :: t2) as tx.
  assert (locked_by tx 0 = tid). {
    rewrite Heqtx; now cbn.
  }
  assert (trace_tid_phase tid tx = 2). {
    assert (trace_tid_phase tid tx >= 2). {
      apply locked_phase; auto.
      now apply sto_trace_app with (t1:=t1a).
    }
    assert (2 >= trace_tid_phase tid tx). {
      rewrite <- H1.
      now apply phase_increase_app.
    }
    omega.
  }

  apply phase_2_preserves_lock; auto.
Qed.

Lemma seq_point_after t1 t2 tid action:
  sto_trace ((tid, action) :: t1 ++ (tid, commit_txn) :: t2)
  -> action = complete_write_item (S (trace_write_version t2))
     \/ action = commit_done_txn.
Proof.
  intros T.
  assert (trace_tid_phase tid (t1 ++ (tid, commit_txn) :: t2) = 4) as TG4. {
    apply sto_trace_cons in T.
    apply commit_phase_app; auto.
    simpl; destruct (Nat.eq_dec tid tid); congruence.
  }
  inversion T; try omega.
  2: now right.
  left.

  assert (trace_write_version (t1 ++ (tid, commit_txn) :: t2) =
          trace_write_version t2). {
    subst.
    clear TG4 val H2 H3 H4 H5.
    inversion T; subst; clear T H4 val.
    remember (t1 ++ (tid, commit_txn) :: t2) as t.
    clear H0.
    revert t1 t2 tid Heqt H2 H3.
    induction H5; intros t1 t2 tid T P L.
    all: destruct t1; simpl in T.
    1,2: congruence.
    all: inversion T.
    all: cbn in *.
    all: destruct (Nat.eq_dec tid tid0); try congruence.
    1-2,5,7,10,13: rewrite <- H3; apply (IHsto_trace _ _ _ H3); auto.
    1-2: rewrite <- H2; apply (IHsto_trace _ _ _ H2); auto.
    1: rewrite <- H4; apply (IHsto_trace _ _ _ H4); auto.

    assert (tid > 0). {
      apply (trace_phase_nonzero _ _ H5); omega.
    }
    omega.

    rewrite <- H3; apply (IHsto_trace _ _ _ H3); auto.
    rewrite H3; apply commit_phase_app.
    rewrite <- H3; auto.
    cbn; destruct (Nat.eq_dec tid tid); congruence.

    assert (tid > 0). {
      apply (tid_nonzero _ commit_txn _ H5).
      rewrite H4; apply in_or_app; right; now left.
    }
    omega.

    assert (tid > 0). {
      apply (tid_nonzero _ commit_txn _ H5).
      rewrite H4; apply in_or_app; right; now left.
    }
    omega.
  }

  now rewrite H6.
Qed.
