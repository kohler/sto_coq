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
Definition heap := address -> option (value * lock * version).
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

Fixpoint tid_phase tid t: nat :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then action_phase a
    else tid_phase tid t'
  | [] => 0
  end.

Lemma tid_phase_head tid a t:
  tid_phase tid ((tid, a) :: t) = action_phase a.
Proof.
  cbn; destruct (Nat.eq_dec tid tid); congruence.
Qed.

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
    -> tid_phase tid t = 0
    -> sto_trace t
    -> sto_trace ((tid, start_txn)::t)

| read_item_step: forall t tid,
    tid_phase tid t = 1
    -> locked_by t 0 = 0
    -> sto_trace t
    -> sto_trace ((tid, read_item (trace_write_version t)) :: t)

| write_item_step: forall t tid val,
    tid_phase tid t = 1
    -> sto_trace t
    -> sto_trace ((tid, write_item val) :: t)

| try_commit_txn_step: forall t tid,
    tid_phase tid t = 1
    -> sto_trace t
    -> sto_trace ((tid, try_commit_txn)::t)

| lock_write_item_step: forall t tid v,
    tid_phase tid t = 2
    -> In (tid, write_item v) t
    -> locked_by t 0 = 0
    -> sto_trace t
    -> sto_trace ((tid, lock_write_item) :: t)

(*sequential point*)
| seq_point_step: forall t tid,
    tid_phase tid t = 2
    -> (forall v, In (tid, write_item v) t
                  -> In (tid, lock_write_item) t)
    -> sto_trace t
    -> sto_trace ((tid, seq_point) :: t)

| validate_read_item_step: forall t tid vers,
    tid_phase tid t = 3
    -> locked_by t tid = tid (* unlocked or locked by me *)
    -> trace_write_version t = vers
    -> sto_trace t
    -> sto_trace ((tid, validate_read_item vers) :: t)

| abort_txn_step: forall t tid,
    tid_phase tid t > 0
    -> tid_phase tid t < 4
    -> sto_trace t
    -> sto_trace ((tid, abort_txn) :: t)

| unlock_item_step: forall t tid,
    tid_phase tid t = 6
    -> locked_by t 0 = tid
    -> sto_trace t
    -> sto_trace ((tid, unlock_write_item) :: t)

| commit_txn_step: forall t tid,
    tid_phase tid t = 3
    -> (forall vers, In (tid, read_item vers) t
                     -> In (tid, validate_read_item vers) t)
    -> sto_trace t
    -> sto_trace ((tid, commit_txn) :: t)

| complete_write_item_step: forall t tid val,
    tid_phase tid t = 4
    -> locked_by t 0 = tid
    -> trace_tid_last_write tid t = Some val
    -> sto_trace t
    -> sto_trace ((tid, complete_write_item (S (trace_write_version t))) :: t)

| commit_done_step: forall t tid,
    tid_phase tid t = 4
    -> locked_by t 0 <> tid
    -> ~ In (tid, commit_done_txn) t
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

Lemma phase_increase_head tid a t:
  sto_trace ((tid, a) :: t) ->
  action_phase a >= tid_phase tid t.
Proof.
  intros; inversion H; cbn; omega.
Qed.

Lemma phase_increase_app tid t1 t2:
  sto_trace (t1 ++ t2) ->
  tid_phase tid (t1 ++ t2) >= tid_phase tid t2.
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
  tid_phase tid t >= action_phase a.
Proof.
  intros H I; apply in_split in I.
  destruct I as [l1 [l2 L]].
  assert (tid_phase tid ((tid, a) :: l2) = action_phase a). {
    apply tid_phase_head.
  }
  rewrite L in *; rewrite <- H0; now apply phase_increase_app.
Qed.

Lemma phase_increase_in_app tid a (t1 t2:trace):
  sto_trace (t1 ++ t2) ->
  In (tid, a) (t1 ++ t2) ->
  action_phase a > tid_phase tid t2 ->
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
  tid_phase tid t > 0 ->
  exists a, In (tid, a) t.
Proof.
  induction t; intros; cbn in *.
  omega.
  destruct a.
  destruct (Nat.eq_dec tid n).
  exists a; subst; now left.
  apply IHt in H; destruct H as [a' H]; exists a'; now right.
Qed.

Lemma trace_in_nonzero tid a t:
  sto_trace t ->
  In (tid, a) t ->
  tid > 0.
Proof.
  revert tid a; induction t.
  - intros tid a H I; destruct I.
  - intros tid' a' H I.
    destruct I; [ | now apply (IHt _ _ (sto_trace_cons _ _ H)) in H0 ].
    subst; inversion H; auto.
    all: assert (tid_phase tid' t > 0) as GZ by omega.
    all: apply trace_phase_in in GZ.
    all: destruct GZ as [a GZ].
    all: now apply (IHt tid' a).
Qed.

Lemma trace_phase_nonzero tid t:
  sto_trace t ->
  tid_phase tid t > 0 ->
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
    apply trace_in_nonzero with (a:=a) (t:=(tid', a)::t); cbn; auto.
  }
  inversion T; subst; cbn; auto.
  right; right; right; eauto.
Qed.

Lemma locked_phase tid t:
  sto_trace t ->
  locked_by t 0 = tid ->
  tid > 0 ->
  tid_phase tid t >= 2.
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
  tid_phase tid t = 4 ->
  tid_phase tid (p :: t) = 4.
Proof.
  destruct p as [tid' a]; intros T Fo; inversion T; cbn in *.
  all: destruct (Nat.eq_dec tid tid'); auto.
  all: subst; omega.
Qed.

Lemma commit_phase_app tid t1 t2:
  sto_trace (t1 ++ t2) ->
  tid_phase tid t2 = 4 ->
  tid_phase tid (t1 ++ t2) = 4.
Proof.
  induction t1; intros.
  now simpl.
  rewrite <- app_comm_cons in *.
  apply commit_phase_cons; auto.
  apply IHt1; auto.
  now apply sto_trace_cons in H.
Qed.

Lemma abort_phase_cons tid p t:
  sto_trace (p :: t) ->
  tid_phase tid t = 6 ->
  tid_phase tid (p :: t) = 6.
Proof.
  destruct p as [tid' a]; intros T Fo; inversion T; cbn in *.
  all: destruct (Nat.eq_dec tid tid'); auto.
  all: subst; omega.
Qed.

Lemma abort_phase_app tid t1 t2:
  sto_trace (t1 ++ t2) ->
  tid_phase tid t2 = 6 ->
  tid_phase tid (t1 ++ t2) = 6.
Proof.
  induction t1; intros.
  now simpl.
  rewrite <- app_comm_cons in *.
  apply abort_phase_cons; auto.
  apply IHt1; auto.
  now apply sto_trace_cons in H.
Qed.


Lemma phase_2_preserves_lock tid t1 t2:
  sto_trace (t1 ++ t2) ->
  tid_phase tid (t1 ++ t2) = 2 ->
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
      assert (tid_phase tid' t2 >= 2). {
        apply locked_phase.
        now apply sto_trace_app with (t1:=(tid',try_commit_txn)::t1).
        auto.
        apply trace_in_nonzero with (a:=try_commit_txn) (t:=(tid', try_commit_txn)::t1 ++ t2).
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

Lemma locked_at_seq_point tid t1 t2 v:
  sto_trace ((tid, seq_point) :: t1 ++ (tid, write_item v) :: t2) ->
  locked_by (t1 ++ (tid, write_item v) :: t2) 0 = tid.
Proof.
  intros T.
  inversion T.
  assert (tid > 0) as TG. {
    apply trace_in_nonzero with (a:=write_item v) (t:=t); rewrite H0; auto.
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
  assert (tid_phase tid tx = 2). {
    assert (tid_phase tid tx >= 2). {
      apply locked_phase; auto.
      now apply sto_trace_app with (t1:=t1a).
    }
    assert (2 >= tid_phase tid tx). {
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
  assert (tid_phase tid (t1 ++ (tid, commit_txn) :: t2) = 4) as TG4. {
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
    all: match goal with
         | [ H: ?t = ?t1 ++ (?tid, commit_txn) :: ?t2 |- _ ] =>
           rename H into Teq
         end.
    all: try solve [ rewrite <- Teq; apply (IHsto_trace _ _ _ Teq); auto ].
    all: assert (tid > 0)
      by (apply (trace_in_nonzero _ commit_txn _ H5);
          rewrite Teq; apply in_or_app; right; now left).
    all: try omega.

    rewrite <- Teq; apply (IHsto_trace _ _ _ Teq); auto.
    rewrite Teq; apply commit_phase_app.
    rewrite <- Teq; auto.
    cbn; destruct (Nat.eq_dec tid tid); congruence.
  }

  now rewrite H6.
Qed.

Lemma unlocked_after_commit_done tid t1 t2:
  sto_trace (t1 ++ (tid, commit_done_txn) :: t2) ->
  locked_by (t1 ++ (tid, commit_done_txn) :: t2) 0 <> tid.
Proof.
  intros T.
  assert (tid > 0) as G. {
    apply (trace_in_nonzero tid commit_done_txn _ T).
    apply in_or_app; right; now left.
  }
  induction t1; cbn in *.
  inversion T; auto.
  destruct a; destruct a.
  all: try solve [ apply IHt1; now apply sto_trace_cons in T ].
  2, 3: omega.
  assert (tid_phase tid (t1 ++ (tid, commit_done_txn) :: t2) = 4) as P4. {
    apply commit_phase_app; auto.
    now apply sto_trace_cons in T.
    cbn; destruct (Nat.eq_dec tid tid); congruence.
  }
  inversion T.
  destruct (Nat.eq_dec t tid); try congruence.
Qed.

Lemma no_steps_after_commit_done tid tid' a t1 t2:
  sto_trace ((tid', a) :: t1 ++ (tid, commit_done_txn) :: t2) ->
  tid <> tid'.
Proof.
  intros T.
  assert (tid_phase tid (t1 ++ (tid, commit_done_txn) :: t2) = 4) as P4. {
    apply commit_phase_app.
    now apply sto_trace_cons in T.
    cbn; destruct (Nat.eq_dec tid tid); congruence.
  }
  remember (t1 ++ (tid, commit_done_txn) :: t2) as t.
  inversion T; try congruence.
  all: destruct (Nat.eq_dec tid tid'); auto.
  all: rewrite <- e in *; clear e.
  - omega.
  - assert (locked_by t 0 <> tid). {
      rewrite Heqt in *; now apply unlocked_after_commit_done.
    }
    congruence.
  - assert (In (tid, commit_done_txn) t). {
      rewrite Heqt; apply in_or_app; right; now left.
    }
    contradiction.
Qed.

Fixpoint seq_list' (t:trace) (c:list nat) : list nat :=
  match t with
  | (tid, commit_txn) :: t' => seq_list' t' (tid :: c)
  | (tid, seq_point) :: t' =>
    match count_occ Nat.eq_dec c tid with
    | 0 => seq_list' t' c
    | S _ => tid :: seq_list' t' c
    end
  | _ :: t' => seq_list' t' c
  | [] => []
  end.

Definition seq_list t := seq_list' t [].

Eval compute in seq_list example_txn.

Eval compute in seq_list example_txn2.

Fixpoint serialize_by (t:trace) (c:list nat) : trace :=
  match c with
  | tid :: c' =>
    filter (fun x => if Nat.eq_dec tid (fst x) then true else false) t
           ++ serialize_by t c'
  | [] => []
  end.

Definition serialize (t:trace) : trace :=
  serialize_by t (seq_list t).

Lemma commit_in_phase4 tid t:
  sto_trace t ->
  tid_phase tid t = 4 ->
  In (tid, commit_txn) t.
Proof.
  intros T; induction T; intros P; cbn in *.
  all: try destruct (Nat.eq_dec tid tid0); try omega.
  all: try solve [right; now apply IHT].
  all: subst.
  1: now left.
  all: right; now apply IHT.
Qed.  

Lemma seq_point_in_phase3 tid t:
  sto_trace t ->
  tid_phase tid t = 3 ->
  In (tid, seq_point) t.
Proof.
  intros T; induction T; intros P; cbn in *.
  all: try destruct (Nat.eq_dec tid tid0); try omega.
  all: try solve [right; now apply IHT].
  all: subst.
  1: now left.
  right; now apply IHT.
Qed.  

Lemma seq_point_in_commit_head tid t:
  sto_trace ((tid, commit_txn) :: t) ->
  In (tid, seq_point) t.
Proof.
  intros T; inversion T.
  apply (seq_point_in_phase3 tid t H3 H1).
Qed.

Lemma seq_point_in_commit_in tid t1 t2:
  sto_trace (t1 ++ (tid, commit_txn) :: t2) ->
  In (tid, seq_point) t2.
Proof.
  induction t1; intros; simpl in *.
  now apply seq_point_in_commit_head.
  inversion H; now apply IHt1.
Qed.

Fixpoint remove_tid tid (t:trace) :=
  match t with
  | (tid', a) :: t' => if Nat.eq_dec tid tid'
                       then remove_tid tid t'
                       else (tid', a) :: remove_tid tid t'
  | [] => []
  end.

Lemma in_remove_tid tid tid' a t:
  tid <> tid' ->
  In (tid', a) t ->
  In (tid', a) (remove_tid tid t).
Proof.
  induction t; intros NE I; cbn in *; auto.
  destruct a0; destruct (Nat.eq_dec tid n); destruct or I.
  inversion I; congruence.
  auto.
  now left.
  right; auto.
Qed.

Lemma remove_tid_in tid x t:
  In x (remove_tid tid t) ->
  In x t.
Proof.
  induction t; intros I; cbn in *; auto.
  destruct a; destruct (Nat.eq_dec tid t0).
  right; auto.
  destruct I; [ left | right ]; auto.
Qed.

Lemma remove_tid_phase tid tid' t:    
  tid <> tid' ->
  tid_phase tid' (remove_tid tid t) = tid_phase tid' t.
Proof.
  induction t; intros NE; cbn in *; auto.
  destruct a.
  destruct (Nat.eq_dec tid t0); destruct (Nat.eq_dec tid' t0);
    subst; cbn; auto.
  contradiction.
  destruct (Nat.eq_dec t0 t0); [ subst; auto | contradiction ].
  cbn; destruct (Nat.eq_dec tid' t0); [ subst; contradiction | auto ].
Qed.

Lemma remove_tid_write_version tid t:
  sto_trace t ->
  tid_phase tid t <> 4 ->
  trace_write_version (remove_tid tid t) = trace_write_version t.
Proof.
  intros T; induction T; intros P; cbn in *; auto.
  all: destruct (Nat.eq_dec tid tid0); [ rewrite e in * | ].
  all: try solve [ apply IHT; omega ].
  contradiction.
  now cbn.
Qed.

Lemma remove_tid_zero t:
  sto_trace t ->
  remove_tid 0 t = t.
Proof.
  induction t; cbn in *; auto; intros.
  destruct a.
  assert (t0 > 0). {
    apply trace_in_nonzero with (a:=a) (t:=(t0, a)::t); auto.
    now left.
  }
  destruct t0; [ omega | ].
  assert (sto_trace t) by (inversion H; auto).
  now rewrite (IHt H1).
Qed.

Lemma locked_by_unlocked_in tid t:
  (forall x, In x t -> fst x > 0) ->
  locked_by t 0 = 0 ->
  locked_by t tid = tid.
Proof.
  induction t; intros A L; cbn in *; auto.
  destruct a; destruct a.
  all: try solve [ apply IHt; auto ].
  assert (n > 0). {
    replace n with (fst (n, lock_write_item)).
    apply A; now left.
    now simpl.
  }
  omega.
  all: reflexivity.
Qed.

Lemma locked_by_unlocked tid t:
  sto_trace t ->
  locked_by t 0 = 0 ->
  locked_by t tid = tid.
Proof.
  intros T L; apply locked_by_unlocked_in; auto.
  intros x I; destruct x; simpl.
  now apply (trace_in_nonzero _ a t).
Qed.

Lemma locked_by_self tid t:
  sto_trace t ->
  locked_by t 0 = tid ->
  locked_by t tid = tid.
Proof.
  intros T; induction T; cbn in *; intros L; auto.
Qed.

Lemma locked_by_other tid tid' t:
  sto_trace t ->
  tid' > 0 ->
  locked_by t 0 = tid' ->
  locked_by t tid = tid'.
Proof.
  intros T; induction T; cbn in *; intros N L; auto.
  all: omega.
Qed.

Lemma remove_tid_locked_by_neq tid tid' t:
  sto_trace t ->
  locked_by t tid <> tid ->
  locked_by (remove_tid tid t) tid' = locked_by t tid'.
Proof.
  intros T; induction T; intros L; cbn in *; auto.
  all: destruct (Nat.eq_dec tid tid0); auto.
  all: congruence.
Qed.

Lemma remove_tid_locked_by_eq tid tid' t:
  sto_trace t ->
  locked_by t tid = tid ->
  locked_by (remove_tid tid t) tid' = tid'.
Proof.
  intros T; induction T; intros L; cbn in *; auto.
  all: destruct (Nat.eq_dec tid tid0); auto.
  apply IHT; apply locked_by_unlocked; auto.
  congruence.
  all: apply IHT; apply locked_by_self; auto; now rewrite e.
Qed.

Lemma remove_tid_last_write tid tid' t:
  tid <> tid' ->
  trace_tid_last_write tid' (remove_tid tid t) = trace_tid_last_write tid' t.
Proof.
  induction t; intros N; cbn in *; auto.
  destruct a; destruct a;
    destruct (Nat.eq_dec tid' t0); destruct (Nat.eq_dec tid t0);
      cbn; auto.
  all: try congruence.
  all: destruct (Nat.eq_dec tid' t0); try congruence; auto.
Qed.

Lemma trace_noncommitted_irrelevant tid t:
  sto_trace t ->
  tid_phase tid t <> 4 ->
  sto_trace (remove_tid tid t).
Proof.
  intros T; induction T; intros P; cbn in *; auto.
  all: destruct (Nat.eq_dec tid tid0);
    [ subst; try solve [apply IHT; omega] | ].
  all: try solve
           [ constructor; auto; rewrite (remove_tid_phase _ _ _ n); auto ].

  {
    rewrite <- (remove_tid_write_version _ _ T P); constructor.
    now rewrite remove_tid_phase.
    rewrite remove_tid_locked_by_eq; auto; now apply locked_by_unlocked.
    auto.
  }    

  {
    apply lock_write_item_step with (v:=v).
    now rewrite remove_tid_phase.
    apply in_remove_tid; auto.
    rewrite remove_tid_locked_by_eq; auto; now apply locked_by_unlocked.
    auto.
  }

  {
    constructor.
    rewrite (remove_tid_phase _ _ _ n); auto.
    intros v I.
    apply in_remove_tid; auto.
    apply (H0 v).
    apply (remove_tid_in _ _ _ I).
    auto.
  }

  {
    constructor.
    rewrite (remove_tid_phase _ _ _ n); auto.
    destruct (Nat.eq_dec (locked_by t tid) tid);
      [ rewrite remove_tid_locked_by_eq | rewrite remove_tid_locked_by_neq ];
      auto.
    rewrite remove_tid_write_version; auto.
    auto.
  }

  {
    constructor.
    rewrite (remove_tid_phase _ _ _ n); auto.
    assert (locked_by t tid <> tid). {
      rewrite locked_by_other with (tid':=tid0); auto.
      apply trace_phase_nonzero with (t:=t); auto; omega.
    }
    rewrite remove_tid_locked_by_neq; auto.
    auto.
  }

  {
    constructor.
    rewrite (remove_tid_phase _ _ _ n); auto.
    intros vers I.
    apply in_remove_tid; auto.
    apply H0.
    apply (remove_tid_in tid); auto.
    auto.
  }

  {
    rewrite <- (remove_tid_write_version _ _ T P).
    apply complete_write_item_step with (val:=val).
    now rewrite remove_tid_phase.
    assert (locked_by t tid <> tid). {
      rewrite locked_by_other with (tid':=tid0); auto.
      apply trace_phase_nonzero with (t:=t); auto; omega.
    }
    rewrite remove_tid_locked_by_neq; auto.
    rewrite remove_tid_last_write; auto.
    auto.
  }

  {
    constructor.
    now rewrite remove_tid_phase.
    destruct (Nat.eq_dec (locked_by t tid) tid);
      [ rewrite remove_tid_locked_by_eq | rewrite remove_tid_locked_by_neq ];
      auto.
    assert (tid0 > 0). {
      apply trace_phase_nonzero with (t:=t); auto; omega.
    }
    omega.
    intros I; apply H1; now apply remove_tid_in with (tid0:=tid).
    auto.
  }
Qed.

Lemma tid_phase_swap tid t1 t2 tid1 tid2 a1 a2:
  tid1 <> tid2 ->
  tid_phase tid (t1 ++ (tid1, a1) :: (tid2, a2) :: t2) =
  tid_phase tid (t1 ++ (tid2, a2) :: (tid1, a1) :: t2).
Proof.
  induction t1; intros NE; cbn in *; auto.
  destruct (Nat.eq_dec tid tid1); destruct (Nat.eq_dec tid tid2);
    congruence.
  destruct a; destruct (Nat.eq_dec tid n); auto.
Qed.

Lemma write_version_swap t1 t2 tid1 tid2 a1 a2:
  action_phase a1 < 4 ->
  trace_write_version (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) =
  trace_write_version (t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
Proof.
  induction t1; intros AP; cbn in *.

  destruct a1; try solve [ cbn in AP; omega ].
  1-8: destruct a2; auto.

  destruct a; repeat rewrite (IHt1 AP); auto.
Qed.

Lemma locked_by_swap_head t1 t2 tid1 tid2 a1 a2 tid:
  locked_by ((tid2, a2) :: (tid1, a1) :: t2) tid =
  locked_by ((tid1, a1) :: (tid2, a2) :: t2) tid ->
  locked_by (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) tid =
  locked_by (t1 ++ (tid1, a1) :: (tid2, a2) :: t2) tid.
Proof.
  induction t1; cbn; auto.
  intros; destruct a; destruct a.
  all: try solve [now apply IHt1].
  all: congruence.
Qed.

Lemma in_middle_swap_iff {A:Type} (t1 t2:list A) p1 p2 p:
  In p (t1 ++ p1 :: p2 :: t2) <-> In p (t1 ++ p2 :: p1 :: t2).
Proof.
  split; intros.
  1: apply Permutation_in with (l:=t1 ++ p1 :: p2 :: t2); auto.
  2: apply Permutation_in with (l:=t1 ++ p2 :: p1 :: t2); auto.
  all: apply Permutation_app_head.
  all: now apply perm_swap.
Qed.

Lemma trace_swap_forward_1 t1 t2 tid1 tid2 a1 a2:
  sto_trace ((tid1, commit_txn) :: t1 ++ (tid2, a2) :: (tid1, a1) :: t2) ->
  action_phase a1 < 3 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, commit_txn) :: t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
Proof.
  revert t2; induction t1; intros t2 T AP N.

  {
    inversion T.
    cbn in *.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    destruct (Nat.eq_dec tid1 tid1); [ omega | congruence ].
  }

  inversion T.
  constructor.
  rewrite tid_phase_swap; auto.
  intros vers I; rewrite in_middle_swap_iff.
  apply H2; rewrite app_comm_cons; now rewrite in_middle_swap_iff.
  rewrite <- app_comm_cons.
  clear tid0 H H0.
  inversion H3.

  constructor; auto.
  rewrite tid_phase_swap; auto.
  apply IHt1.
  {
    cbn in *.
    omega.
  }
    rename H3 into T1; inversion T1.
  
  inversion H3.
  inversion H9.
  simpl.
  clear T H tid0.
  rewrite <- H0 in H3.
  rename H3 into T.
  revert tid1 tid2 N H1 H2 H0.


Lemma trace_swap_forward t1 t2 tid1 tid2 a1 a2:
  sto_trace (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) ->
  tid_phase tid1 (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) = 4 ->
  action_phase a1 < 3 ->
  tid1 <> tid2 ->
  sto_trace (t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
Proof.
  unfold Top.tid in *.
  intros T P AP NE; remember (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) as t.
  revert t1 t2 tid1 tid2 a1 a2 Heqt P AP NE.
  induction T; intros t1 t2 tid1 tid2 a1 a2 ET P AP NE.
  destruct t1; cbn in *; discriminate.

  {
    destruct t1; cbn in *; inversion ET; subst.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    constructor; auto.
    rewrite tid_phase_swap; auto.
  }

  {
    destruct t1; cbn in *; inversion ET; subst.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    rewrite write_version_swap; auto.
    constructor; auto.
    rewrite tid_phase_swap; auto.
    rewrite locked_by_swap_head; auto.

    assert (sto_trace ((tid2, a2) :: (tid1, a1) :: t2)) as TH. {
      now apply sto_trace_app with (t1:=t1).
    }
    assert (tid1 > 0) as T1N. {
      apply (trace_in_nonzero _ a1 _ TH).
      right; now left.
    }
    destruct a1; destruct a2; try reflexivity.
    all: try solve [simpl in AP; omega].
    all: inversion TH.
    simpl in H5; omega.
    simpl in H4; omega.
    simpl in H5; omega.
  }

  {
    destruct t1; cbn in *; inversion ET; subst.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    constructor; auto.
    rewrite tid_phase_swap; auto.
  }

  {
    destruct t1; cbn in *; inversion ET; subst.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    constructor; auto.
    rewrite tid_phase_swap; auto.
  }

  {
    destruct t1; cbn in *; inversion ET; subst.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    apply lock_write_item_step with (v:=v); auto.
    rewrite tid_phase_swap; auto.
    apply Permutation_in with (l:=t1 ++ (tid2, a2) :: (tid1, a1) :: t2); auto.
    apply Permutation_app_head; constructor.
    rewrite locked_by_swap_head; auto.

    assert (sto_trace ((tid2, a2) :: (tid1, a1) :: t2)) as TH. {
      now apply sto_trace_app with (t1:=t1).
    }
    assert (tid1 > 0) as T1N. {
      apply (trace_in_nonzero _ a1 _ TH).
      right; now left.
    }
    destruct a1; destruct a2; try reflexivity.
    all: try solve [simpl in AP; omega].
    all: inversion TH.
    simpl in H6; omega.
    simpl in H5; omega.
    simpl in H6; omega.
  }

  {
    destruct t1; cbn in *; inversion ET; subst.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    constructor; auto.
    rewrite tid_phase_swap; auto.
    intros v I.
    apply Permutation_in with (l:=t1 ++ (tid2, a2) :: (tid1, a1) :: t2).
    apply Permutation_app_head; constructor.
    apply (H0 v).
    apply Permutation_in with (l:=t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
    apply Permutation_app_head; constructor.
    auto.
  }

  {
    destruct t1; cbn in *; inversion ET; subst.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    constructor; auto.
    rewrite tid_phase_swap; auto.
    rewrite locked_by_swap_head; auto.

    {
      assert (sto_trace ((tid2, a2) :: (tid1, a1) :: t2)) as TH. {
        now apply sto_trace_app with (t1:=t1).
      }
      assert (tid1 > 0) as T1N. {
        apply (trace_in_nonzero _ a1 _ TH).
        right; now left.
      }
      destruct a1; destruct a2; try reflexivity.
      all: try solve [simpl in AP; omega].
      all: inversion TH.
      simpl in H5; omega.
      simpl in H4; omega.
      simpl in H5; omega.
    }

    rewrite <- write_version_swap; auto.
  }

  {
    destruct t1; cbn in *; inversion ET; subst.
    destruct (Nat.eq_dec tid1 tid2); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    constructor; auto.
    rewrite tid_phase_swap; auto.
    rewrite tid_phase_swap; auto.
  }

  {
    destruct t1; cbn in *; inversion ET.
    rewrite <- H2 in *; rewrite H4 in *; rewrite <- H3 in *; clear H2 H3 H4.
    destruct (Nat.eq_dec tid1 tid0); [ congruence | ].
    rewrite tid_phase_head in P; omega.
    destruct (Nat.eq_dec tid1 tid0); [ omega | ].

    rewrite H3 in *; clear H3.
    constructor; auto.
    rewrite tid_phase_swap; auto.
    rewrite locked_by_swap_head; auto.

    {
      assert (sto_trace ((tid2, a2) :: (tid1, a1) :: t2)) as TH. {
        now apply sto_trace_app with (t1:=t1).
      }
      assert (tid1 > 0) as T1N. {
        apply (trace_in_nonzero _ a1 _ TH).
        right; now left.
      }
      destruct a1; destruct a2; try reflexivity.
      all: try solve [simpl in AP; omega].
      all: inversion TH.
      simpl in H6; omega.
      simpl in H5; omega.
      simpl in H6; omega.
    }
  }

  {
    destruct t1; cbn in *; inversion ET.
    {
      subst.
      rewrite tid_phase_head in P.
      destruct (Nat.eq_dec tid1 tid2); [ | omega ].
      subst; clear P; congruence.
    }
    rewrite <- H2 in *; clear p H2.
    rewrite H3 in *; clear t H3 ET.

    constructor; auto.
    rewrite tid_phase_swap; auto.
    {
      intros vers I.
      apply Permutation_in with (l:=t1 ++ (tid2, a2) :: (tid1, a1) :: t2).
      apply Permutation_app_head; constructor.
      apply (H0 vers).
      apply Permutation_in with (l:=t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
      apply Permutation_app_head; constructor.
      auto.
    }
    destruct (Nat.eq_dec tid1 tid0); auto.
    rewrite <- e in *; clear e tid0 P.
    admit.
  }

  {
    destruct t1; cbn in *; inversion ET.
    {
      rewrite H3 in *; rewrite H5 in *; clear t tid0 H3 H5.
      rewrite tid_phase_head in P.
      destruct (Nat.eq_dec tid1 tid2); [ congruence | omega ].
    }
    rewrite <- H3 in *; rewrite H4 in *; clear p t H3 H4 ET.
    destruct (Nat.eq_dec tid1 tid0); auto.
    Focus 2.
    rewrite write_version_swap; [ | omega].
    apply complete_write_item_step with (val:=val).
    rewrite tid_phase_swap; auto.
    constructor.
    eeFocus 2. auto.
    apply IHT; auto.
    rewrite tid_phase_swap; auto.
    
    rewrite locked_by_swap_head; auto.

    {
      assert (sto_trace ((tid2, a2) :: (tid1, a1) :: t2)) as TH. {
        now apply sto_trace_app with (t1:=t1).
      }
      assert (tid1 > 0) as T1N. {
        apply (trace_in_nonzero _ a1 _ TH).
        right; now left.
      }
      destruct a1; destruct a2; try reflexivity.
      all: try solve [simpl in AP; omega].
      all: inversion TH.
      simpl in H6; omega.
      simpl in H5; omega.
      simpl in H6; omega.
    }
    

Lemma count_occ_app {A:Type} eq_dec (l1 l2:list A) x:
  count_occ eq_dec (l1 ++ l2) x =
  count_occ eq_dec l1 x + count_occ eq_dec l2 x.
Proof.
  induction l1; cbn; auto.
  destruct (eq_dec a x); auto.
  rewrite IHl1; omega.
Qed.

Lemma in_seq_list_subset tid t c1 c2:
  In tid (seq_list' t c2) ->
  (forall x, In x c2 -> In x c1) ->
  In tid (seq_list' t c1).
Proof.
  revert c1 c2; induction t; intros; cbn; auto.
  destruct a; destruct a; try solve [now apply (IHt c1 c2)].
  cbn in H.
  remember (count_occ Nat.eq_dec c2 t0) as c2ct; destruct c2ct.
  destruct (count_occ Nat.eq_dec c1 t0).
  now apply (IHt c1 c2).
  right; now apply (IHt c1 c2).
  assert (In t0 c1). {
    apply H0.
    rewrite (count_occ_In Nat.eq_dec); omega.
  }
  rewrite (count_occ_In Nat.eq_dec) in H1.
  destruct (count_occ Nat.eq_dec c1 t0); try omega.
  destruct H; [ left; auto | right; now apply (IHt c1 c2) ].
  cbn in H.
  assert (forall x, In x (t0 :: c2) -> In x (t0 :: c1)). {
    intros x I; destruct I; [ left | right ]; auto.
  }
  now apply (IHt (t0::c1) (t0::c2)).
Qed.

Lemma count_occ_Permutation {A:Type} eq_dec (l1 l2:list A) a:
  Permutation l1 l2 ->
  count_occ eq_dec l1 a = count_occ eq_dec l2 a.
Proof.
  intros P; induction P; auto; cbn.
  - destruct (eq_dec x a); now rewrite IHP.
  - destruct (eq_dec x a); destruct (eq_dec y a); auto.
  - rewrite IHP1; now rewrite IHP2.
Qed.

Lemma in_seq_list_Permutation tid t c1 c2:
  Permutation c1 c2 ->
  In tid (seq_list' t c1) ->
  In tid (seq_list' t c2).
Proof.
  intros P I.
  apply in_seq_list_subset with (c2:=c1); auto.
  intros x E; apply Permutation_in with (l:=c1); auto.
Qed.

Lemma in_seq_list_or tid t x c:
  In tid (seq_list' t (x :: c)) ->
  tid = x \/ In tid (seq_list' t c).
Proof.
  revert x c; induction t; intros; cbn; auto.
  destruct a; destruct a; try solve [now apply (IHt x c)].
  - cbn in H.
    destruct (Nat.eq_dec x t0).
    + destruct H; [ subst; now left | ].
      apply IHt in H; destruct or H; [ now left | right ].
      destruct (count_occ Nat.eq_dec c t0); auto.
      now right.
    + destruct (count_occ Nat.eq_dec c t0).
      apply IHt in H; destruct or H; auto.
      destruct H; [ right; subst; now left | ].
      apply IHt in H; destruct or H; [ now left | right ].
      now right.
  - cbn in H.
    assert (Permutation (t0::x::c) (x::t0::c)) by (apply perm_swap).
    apply (in_seq_list_Permutation _ _ _ _ H0) in H; clear H0.
    apply (IHt _ _ H).
Qed.  

Lemma commit_seq_point_in_seq_list tid (t1 t2 t3:trace):
  In tid (seq_list (t1 ++ (tid, commit_txn) :: t2 ++ (tid, seq_point) :: t3)).
Proof.
  induction t1.
  cbn.
  induction t2.
  cbn; destruct (Nat.eq_dec tid tid).
  cbn; now left.
  congruence.
  destruct a; destruct a; cbn; auto.
  destruct (Nat.eq_dec tid t).
  rewrite e; now left.
  auto.
  apply in_seq_list_subset with (c2:=[tid]); auto.
  intros x I; destruct I; right; now left.

  destruct a; destruct a; simpl; cbn; auto.
  apply in_seq_list_subset with (c2:=[]); auto.
  intros x I; destruct I.
Qed.

Lemma in_seq_list_iff tid t:
  sto_trace t ->
  tid_phase tid t = 4 <-> In tid (seq_list t).
Proof.
  intros T; split.

  intros P.
  apply commit_in_phase4 in P.
  apply in_split in P.
  destruct P as [t1 [t2 TE]].
  assert (In (tid, seq_point) t2). {
    apply seq_point_in_commit_in with (t1:=t1).
    now rewrite TE in T.
  }
  apply in_split in H.
  destruct H as [t2' [t3 TE']].
  rewrite TE; rewrite TE'.
  apply commit_seq_point_in_seq_list.
  auto.

  induction T; intros I; cbn in *; try contradiction.
  all: try apply IHT in I.
  all: destruct (Nat.eq_dec tid tid0); auto.
  all: try solve [rewrite <- e in *; rewrite I in *; omega].
  apply IHT.
  apply in_seq_list_or in I.
  destruct I; auto; congruence.
Qed.

Lemma serialize_not_in_head tid a t c:
  ~ In tid c ->
  serialize_by ((tid, a) :: t) c = serialize_by t c.
Proof.
  induction c; intros NI; cbn; auto.
  destruct (Nat.eq_dec a0 tid).
  rewrite e in NI; destruct NI; now left.
  assert (~ In tid c) as NIX. {
    contradict NI; now right.
  }
  now rewrite (IHc NIX).
Qed.

Lemma serialize_trace t:
  sto_trace t ->
  sto_trace (serialize t).
Proof.
  intros T; induction T; cbn in *; auto.
  1-9: match goal with
       | [ |- context [ (?tid, ?a) :: ?t ] ] =>
         assert (tid_phase tid ((tid, a) :: t) <> 4) as NP by
             (cbn; destruct (Nat.eq_dec tid tid); omega)
       end.
  1-9: rewrite in_seq_list_iff in NP; cbn in NP; auto.
  6: now apply lock_write_item_step with (v:=v).
  1-9: now rewrite (serialize_not_in_head _ _ _ _ NP).
  Focus 2.
  
  

  assert (tid_phase tid0 t
  - cbn in *; auto.
  - 