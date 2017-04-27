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
Fixpoint write_version (t:trace): version :=
  match t with
  | (_, complete_write_item v) :: _ => v
  | _ :: t' => write_version t'
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
    -> sto_trace ((tid, read_item (write_version t)) :: t)

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
    -> write_version t = vers
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
    -> sto_trace ((tid, complete_write_item (S (write_version t))) :: t)

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
  -> action = complete_write_item (S (write_version t2))
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

  assert (write_version (t1 ++ (tid, commit_txn) :: t2) =
          write_version t2). {
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

Definition filter_tid tid (t:trace) :=
  filter (fun x => Nat.eqb tid (fst x)) t.

Fixpoint serialize_by (t:trace) (c:list nat) : trace :=
  match c with
  | tid :: c' => filter_tid tid t ++ serialize_by t c'
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
  write_version (remove_tid tid t) = write_version t.
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

Lemma locked_by_self_or tid t:
  locked_by t tid = tid ->
  locked_by t 0 = 0 \/ locked_by t 0 = tid.
Proof.
  induction t; cbn in *; intros.
  now left.
  destruct a; destruct a; try solve [ now apply IHt ].
  all: intuition.
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
  write_version (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) =
  write_version (t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
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

Definition action_internal a :=
  match a with
  | read_item _
  | validate_read_item _
  | lock_write_item
  | complete_write_item _
  | unlock_write_item => False
  | _ => True
  end.

Definition action_commute_read a :=
  match a with
  | lock_write_item
  | complete_write_item _
  | unlock_write_item => False
  | _ => True
  end.

Local Ltac check_action :=
  match goal with
  | [ H: action_internal ?a, H2: ?b = ?a |- _ ] =>
    rewrite <- H2 in *; clear H2; cbn in H; try contradiction; clear H
  | [ H: action_commute_read ?a, H2: ?b = ?a |- _ ] =>
    rewrite <- H2 in *; clear H2; cbn in H; try contradiction; clear H
  | [ H: action_phase ?a < _, H2: ?b = ?a |- _ ] =>
    rewrite <- H2 in *; clear H2; cbn in H; try omega
  end.
Local Ltac fix_phase :=
  match goal with
  | [ TP: tid_phase ?tid ?x = tid_phase ?tid _
      |- context [ tid_phase ?tid ?x ] ] => now rewrite TP
  | [ TP: tid_phase ?tid _ = tid_phase ?tid ?x
      |- context [ tid_phase ?tid ?x ] ] => now rewrite <- TP
  | [ L: locked_by ?t ?a = ?x
      |- locked_by (_ :: ?t) ?a = ?x ] => cbn; apply L
  | [ L: locked_by ?t ?a <> ?x
      |- locked_by (_ :: ?t) ?a <> ?x ] => cbn; apply L
  | [ L: locked_by (_ :: ?t) ?a = ?x
      |- locked_by ?t ?a = ?x ] => cbn in L; apply L
  | [ WV: write_version ?t = ?x
      |- write_version (_ :: ?t) = ?x ] => cbn; apply WV
  | [ LW: trace_tid_last_write ?tid ?t = ?x
      |- trace_tid_last_write ?tid ((?tid2, ?a) :: ?t) = ?x ] =>
    cbn; destruct (Nat.eq_dec tid tid2); [ congruence | apply LW ]
  | [ LW: trace_tid_last_write ?tid ((?tid2, ?a) :: ?t) = ?x
      |- trace_tid_last_write ?tid ?t = ?x ] =>
    cbn in LW; destruct (Nat.eq_dec tid tid2); [ congruence | apply LW ]
  | [ H: In ?p ?t
      |- In ?p (_ :: ?t) ] => right; apply H
  | [ H: In ?p (_ :: ?t)
      |- In ?p ?t ] => destruct H; [ congruence | apply H ]
  | [ |- context [ In (?tid, _) _ ] ] =>
    let vx := fresh in
    let I := fresh in
    intros vx I; destruct I; [ congruence | right; revert vx I; assumption ]
  | [ H: ~ In ?p ?t
      |- ~ In ?p (?x :: ?t) ] => contradict H; destruct H; [ congruence | assumption ]
  | [ H: ~ In ?p (?x :: ?t)
      |- ~ In ?p ?t ] => contradict H; right; assumption
  | [ |- sto_trace ((?tid, start_txn) :: ?t) ] =>
    constructor; [ assumption | fix_phase | auto ]
  | [ |- sto_trace ((?tid, read_item _) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, write_item _) :: ?t) ] =>
    constructor; [ fix_phase | assumption ]
  | [ |- sto_trace ((?tid, try_commit_txn) :: ?t) ] =>
    constructor; [ fix_phase | assumption ]
  | [ H: In (?tid, write_item ?vv) _
      |- sto_trace ((?tid, lock_write_item) :: ?t) ] =>
    apply lock_write_item_step with (v:=vv); [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, seq_point) :: ?t) ] =>
    constructor; [ fix_phase | | assumption ]
  | [ |- sto_trace ((?tid, validate_read_item _) :: ?t) ] =>
    constructor; [ fix_phase .. | | assumption ]
  | [ |- sto_trace ((?tid, abort_txn) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, unlock_write_item) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, commit_txn) :: ?t) ] =>
    constructor; [ fix_phase .. | | assumption ]
  | [ H: trace_tid_last_write ?tid _ = Some ?vx
      |- sto_trace ((?tid, complete_write_item (S (write_version ?t))) :: ?t) ] =>
    apply complete_write_item_step with (val:=vx); [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, commit_done_txn) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | _ => idtac
  end.
Local Ltac chomp1 :=
  match goal with
  | [ |- sto_trace ((?tid, start_txn) :: _ :: _) ] =>
    constructor; [ assumption | | ]; fix_phase
  | [ |- sto_trace ((?tid, read_item (write_version ?t)) :: ?p :: ?t) ] =>
    replace (write_version t) with (write_version (p :: t)) by (now cbn);
    constructor; fix_phase
  | [ |- sto_trace ((?tid, write_item _) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, try_commit_txn) :: _ :: _) ] =>
    constructor; fix_phase
  | [ H: In (?tid, write_item ?vv) _
      |- sto_trace ((?tid, lock_write_item) :: _ :: _) ] =>
    apply lock_write_item_step with (v:=vv); fix_phase
  | [ |- sto_trace ((?tid, seq_point) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, validate_read_item ?vers) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, abort_txn) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, unlock_write_item) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, commit_txn) :: _ :: _) ] =>
    constructor; fix_phase
  | [ H: trace_tid_last_write ?tid _ = Some ?vx
      |- sto_trace ((?tid, complete_write_item (S (write_version ?t))) :: ?p :: ?t) ] =>
    replace (write_version t) with (write_version (p :: t)) by (now cbn);
    apply complete_write_item_step with (val:=vx); fix_phase
  | [ |- sto_trace ((?tid, commit_done_txn) :: _ :: _) ] =>
    constructor; fix_phase
  end.



Lemma trace_swap_internal_back tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  action_internal a2 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T; check_action.
  all: match goal with
       | [ H: sto_trace ((?t1, ?a1) :: ?t), H2: sto_trace (?a :: ?b :: ?c) |- _ ] =>
         rename H into T1
       end.

  - inversion T1; chomp1.
  - inversion T1; chomp1.
  - inversion T1; chomp1.
  - inversion T1; chomp1.
    all: intros vx I.
    all: assert (In (tid2, write_item vx) t0) as II by (rewrite H1; now right).
    all: rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - inversion T1; chomp1.
  - inversion T1; chomp1.
    all: intros vers' I.
    all: assert (In (tid2, read_item vers') t0) as II by (rewrite H1; now right).
    all: rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - assert (tid2 > 0) by (apply (trace_in_nonzero _ commit_done_txn _ T); now left).
    inversion T1; chomp1.
    all: rewrite <- H6 in *; cbn in H3; try assumption.
    rewrite H10; omega.
    all: now rewrite H9.
Qed.

Lemma trace_swap_internal_forward tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  action_internal a1 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T; rewrite <- H0 in *; clear H0.
  all: match goal with
       | [ H: sto_trace ((?t1, ?a1) :: ?t), H2: sto_trace (?a :: ?b :: ?c) |- _ ] =>
         rename H into T1
       end.

  - inversion T1; chomp1.
  - rewrite H1 in *; clear H1.
    replace (write_version ((tid1, a1) :: t)) with (write_version t) in *.
    inversion T1; check_action; chomp1.
    destruct a1; cbn in Int; try contradiction Int; cbn; reflexivity.
  - inversion T1; chomp1.
  - inversion T1; chomp1.
  - inversion T1; check_action; chomp1.
    cbn; congruence.
  - inversion T1; chomp1.
    all: intros vx I.
    all: assert (In (tid2, write_item vx) t0) as II by (rewrite H1; now right).
    all: rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - inversion T1; check_action; subst; chomp1.
    all: cbn; reflexivity.
  - inversion T1; chomp1.
  - inversion T1; check_action; chomp1.
    assert (tid1 > 0) as TZ by (apply (trace_in_nonzero _ commit_done_txn _ T1); now left).
    cbn; omega.
  - inversion T1; chomp1.
    all: intros vers' I.
    all: assert (In (tid2, read_item vers') t0) as II by (rewrite H1; now right).
    all: rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - rewrite H1 in *; clear H1.
    replace (write_version ((tid1, a1) :: t)) with (write_version t) in *.
    inversion T1; check_action; chomp1.
    assert (tid1 > 0) as TZ by (apply (trace_in_nonzero _ commit_done_txn _ T1); now left).
    cbn; omega.
    destruct a1; cbn in Int; try contradiction Int; cbn; reflexivity.
  - assert (tid2 > 0) as TZ by (apply (trace_in_nonzero _ commit_done_txn _ T); now left).
    inversion T1; chomp1.
    all: rewrite <- H5 in *; clear H5.
    all: cbn in H3; try apply H3.
    rewrite H9; omega.
    all: now rewrite H8.
Qed.

Lemma trace_swap_read_back tid1 tid2 v a1 t:
  sto_trace ((tid2, read_item v) :: (tid1, a1) :: t) ->
  action_commute_read a1 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, a1) :: (tid2, read_item v) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, read_item v) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T.
  assert (write_version ((tid1, a1) :: t) = write_version t) as WV. {
    destruct a1; cbn in Int; try contradiction; cbn; reflexivity.
  }
  rewrite WV.
  rename H4 into T1.

  inversion T1; check_action; chomp1.
  all: cbn; destruct (Nat.eq_dec tid1 tid2); [ congruence | auto ].
  constructor; fix_phase; auto.
Qed.

Lemma trace_swap_validate_read_back tid1 tid2 v a1 t:
  sto_trace ((tid2, validate_read_item v) :: (tid1, a1) :: t) ->
  action_commute_read a1 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, a1) :: (tid2, validate_read_item v) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, validate_read_item v) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T.
  assert (write_version ((tid1, a1) :: t) = write_version t) as WV. {
    destruct a1; cbn in Int; try contradiction; cbn; reflexivity.
  }
  rename H5 into T1.

  inversion T1; check_action; chomp1.
  all: cbn in WV; auto.
Qed.

Lemma trace_swap_read_forward tid1 tid2 v a2 t:
  sto_trace ((tid2, a2) :: (tid1, read_item v) :: t) ->
  action_commute_read a2 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, read_item v) :: (tid2, a2) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, read_item v) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T; check_action.
  all: match goal with
       | [ H: sto_trace ((?t1, ?a1) :: ?t), H2: sto_trace (?a :: ?b :: ?c) |- _ ] =>
         rename H into T1
       end.
  all: inversion T1; chomp1.
  - cbn; destruct (Nat.eq_dec tid1 tid2); auto.
  - cbn; fix_phase.
  - intros vx I.
    assert (In (tid2, write_item vx) t0) as II by (rewrite H1; now right).
    rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - rewrite <- H4; cbn; reflexivity.
  - intros vers' I.
    assert (In (tid2, read_item vers') t0) as II by (rewrite H1; now right).
    rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - assert (tid2 > 0) by (apply (trace_in_nonzero _ commit_done_txn _ T); now left).
    omega.
Qed.

Lemma trace_swap_validate_read_forward tid1 tid2 v a2 t:
  sto_trace ((tid2, a2) :: (tid1, validate_read_item v) :: t) ->
  action_commute_read a2 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, validate_read_item v) :: (tid2, a2) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, validate_read_item v) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T; check_action.
  all: match goal with
       | [ H: sto_trace ((?t1, ?a1) :: ?t), H2: sto_trace (?a :: ?b :: ?c) |- _ ] =>
         rename H into T1
       end.
  all: inversion T1; chomp1.
  - cbn; destruct (Nat.eq_dec tid1 tid2); [ congruence | auto ].
  - cbn; fix_phase.
  - intros vx I.
    assert (In (tid2, write_item vx) t0) as II by (rewrite H1; now right).
    rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - rewrite <- H4; cbn; reflexivity.
  - intros vers' I.
    assert (In (tid2, read_item vers') t0) as II by (rewrite H1; now right).
    rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - apply locked_by_self_or in H8.
    destruct H8.
    assert (tid2 > 0) by (apply (trace_in_nonzero _ commit_done_txn _ T); now left).
    omega.
    rewrite H8; auto.
Qed.

Lemma trace_swap_forward_to_seq_point tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  tid1 <> tid2 ->
  action_phase a1 < 3 ->
  locked_by ((tid2, a2) :: t) tid1 = tid1 ->
  write_version ((tid2, a2) :: t) = write_version t ->
  sto_trace ((tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros T N AP LB WV.
  assert (write_version ((tid1, a1) :: t) = write_version t) as WV1. {
    destruct a1; cbn in AP; try omega.
    all: cbn; reflexivity.
  }
  assert (tid1 > 0) as T1Z. {
    apply (trace_in_nonzero _ a1 _ T); right; now left.
  }
  assert (tid2 > 0) as T2Z. {
    apply (trace_in_nonzero _ a2 _ T); now left.
  }
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T; rewrite <- H0 in *; clear H0.
  all: match goal with
       | [ H: sto_trace ((?tid, ?a) :: ?t) |- _ ] => rename H into T1
       end.
  all: try rewrite H1 in *; clear H H1.
  all: try solve [ apply trace_swap_internal_back; [ assumption | now cbn | assumption ] ].
  - rewrite WV1.
    apply trace_swap_read_back; auto.
    rewrite <- WV1; auto.
    destruct a1; cbn in AP; try omega; cbn; auto.
    cbn in H3; omega.
  - cbn in LB; congruence.
  - apply trace_swap_validate_read_back; auto.
    destruct a1; cbn in AP; try omega; cbn; auto.
  - inversion T1; check_action; chomp1.
    all: cbn; auto.
    cbn in H3; congruence.
  - cbn in WV; destruct a1; cbn in AP; try omega.
Qed.    

Definition all_committed (t:trace) :=
  forall tid, tid_phase tid t = 4.

Definition tid_outstanding_read tid (t:trace) :=
  exists v, In (tid, read_item v) t /\
            ~ In (tid, validate_read_item v) t.

Lemma trace_outstanding_read_head tid v t:
  sto_trace ((tid, read_item v) :: t) ->
  tid_outstanding_read tid ((tid, read_item v) :: t).
Proof.
  intros T; inversion T.
  exists (write_version t); split.
  now left.
  intros F; subst.
  assert (3 <= tid_phase tid ((tid, read_item (write_version t)) :: t)). {
    replace 3 with (action_phase (validate_read_item (write_version t))) by (now cbn).
    apply phase_increase_in; auto.
  }
  cbn in H; destruct (Nat.eq_dec tid tid); [ omega | congruence ].
Qed.

Inductive trace_unconflicted : trace -> Prop :=
| nil_unc: trace_unconflicted []
| internal_unc: forall tid a t,
    trace_unconflicted t ->
    action_internal a ->
    trace_unconflicted ((tid, a) :: t)
| read_unc: forall tid v t,
    trace_unconflicted t ->
    locked_by t 0 = 0 ->
    write_version t = v ->
    trace_unconflicted ((tid, read_item v) :: t)
| validate_read_unc: forall tid v t,
    trace_unconflicted t ->
    trace_unconflicted ((tid, validate_read_item v) :: t)
| lock_unc: forall tid t,
    trace_unconflicted t ->
    (forall tid', tid = tid' \/ ~ tid_outstanding_read tid' t) ->
    trace_unconflicted ((tid, lock_write_item) :: t)
| complete_unc: forall tid v t,
    trace_unconflicted t ->
    trace_unconflicted ((tid, complete_write_item v) :: t)
| unlock_unc: forall tid t,
    trace_unconflicted t ->
    trace_unconflicted ((tid, unlock_write_item) :: t).

Lemma phase3_locked tid t:
  sto_trace t ->
  tid_phase tid t < 4 ->
  In (tid, lock_write_item) t ->
  locked_by t 0 = tid.
Proof.
  intros T; induction T; intros P I.
  all: cbn in *; try contradiction.
  all: destruct (Nat.eq_dec tid tid0); try omega.
  all: destruct or I; try congruence; auto.
  all: assert (2 <= tid_phase tid t) as P2
      by (replace 2 with (action_phase lock_write_item) by (now cbn);
          apply phase_increase_in; auto).
  all: try solve [ rewrite <- e in *; omega ].
  - rewrite (IHT P I) in H1.
    assert (tid > 0) by (apply trace_phase_nonzero with (t:=t); auto; omega); omega.
  - rewrite <- e in *; clear e P.
    assert (tid_phase tid t < 4) as TL by omega; auto.
  - rewrite <- e in *; clear e P.
    assert (tid_phase tid t < 4) as TL by omega; auto.
  - rewrite (IHT P I) in H0; congruence.
  - rewrite (IHT P I) in H0; congruence.
Qed.

Lemma committed_write_locked_or_completed tid t:
  sto_trace t ->
  tid_phase tid t = 4 ->
  In (tid, lock_write_item) t ->
  locked_by t 0 = tid \/ exists v, In (tid, complete_write_item v) t.
Proof.
  intros T; induction T; intros P I.
  all: cbn in *; try contradiction.
  all: destruct (Nat.eq_dec tid tid0); try omega.
  all: destruct or I; try congruence.
  all: try solve [ generalize (IHT P I); intros X; destruct X as [X | [vv X]];
                   [ now left | right; exists vv; now right ] ].
  - generalize (IHT P I); intros X; destruct X as [X | [vv X]].
    assert (tid > 0) as NZ by (apply trace_phase_nonzero with (t:=t); auto; omega).
    omega.
    right; exists vv; now right.
  - generalize (IHT P I); intros X; destruct X as [X | [vv X]].
    congruence.
    right; exists vv; now right.
  - rewrite <- e in *; clear e P; left.
    apply phase3_locked; auto; omega.
  - right; exists (S (write_version t)); rewrite e; now left.
  - generalize (IHT P I); intros X; destruct X as [X | [vv X]].
    congruence.
    right; exists vv; now right.
  - rewrite <- e in *; clear e P.
    generalize (IHT H I); intros X; destruct X as [X | [vv X]].
    now left.
    right; exists vv; now right.
Qed.

Lemma committed_read_validated tid t v:
  sto_trace t ->
  tid_phase tid t = 4 ->
  In (tid, read_item v) t ->
  In (tid, validate_read_item v) t.
Proof.
  intros T; induction T; intros P I.
  all: cbn in *; try contradiction.
  all: destruct (Nat.eq_dec tid tid0); try omega.
  all: destruct or I; try congruence.
  all: try solve [ generalize (IHT P I); intros X; now right ].
  - right; rewrite <- e in *; auto.
  - rewrite <- e in *; auto.
  - rewrite <- e in *; auto.
Qed.

Lemma phase_increase_head_middle tid a1 t1 a2 t2:
  sto_trace ((tid, a1) :: t1 ++ (tid, a2) :: t2) ->
  action_phase a2 <= action_phase a1.
Proof.
  intros T.
  replace (action_phase a1) with (tid_phase tid ((tid, a1) :: t1 ++ (tid, a2) :: t2)).
  apply phase_increase_in; auto.
  right; apply in_or_app; right; now left.
  cbn; destruct (Nat.eq_dec tid tid); congruence.
Qed.

Lemma write_version_increase_app t1 t2:
  sto_trace (t1 ++ t2) ->
  write_version t2 <= write_version (t1 ++ t2).
Proof.
  induction t1; intros T.
  cbn; omega.
  destruct a; inversion T; rewrite <- H0 in *; clear H0.
  all: cbn; auto.
Qed.

Lemma read_version_increase_in tid v t:
  sto_trace t ->
  In (tid, read_item v) t ->
  v <= write_version t.
Proof.
  intros T; induction T; intros I.
  destruct I.
  all: destruct I as [I | I]; try congruence.
  all: cbn; auto.
  inversion I; omega.
Qed.

Lemma trace_after_lock tid t1 t2:
  sto_trace (t1 ++ (tid, lock_write_item) :: t2) ->
  In (tid, unlock_write_item) t1
  \/ locked_by (t1 ++ (tid, lock_write_item) :: t2) 0 = tid
  \/ write_version t2 < write_version (t1 ++ (tid, lock_write_item) :: t2).
Proof.
  induction t1; intros T.
  right; left; now cbn.
  destruct a; inversion T; rewrite <- H0 in *; clear H0.
  all: match goal with
       | [ H: sto_trace (_ ++ _ :: _) |- _ ] =>
         rename H into T1; generalize (IHt1 T1); intros X
       end.
  all: destruct X as [X | [X | X]]; intuition.
  - assert (tid > 0). {
      apply (trace_in_nonzero _ lock_write_item _ T1).
      apply in_or_app; right; now left.
    }
    omega.
  - rewrite H3 in X; rewrite X; left; now left.
  - rewrite H3 in X; rewrite X in *; clear X t.
    cbn; right; right.
    apply le_lt_n_Sm.
    apply write_version_increase_app in T1; now cbn in T1.
  - cbn; right; right; omega.
  - cbn; right; right; omega.
  - cbn; right; right; omega.
Qed.
  
Lemma nonaborted_read_validate_different tid tid' t1 t2 v:
  sto_trace (t1 ++ (tid, lock_write_item) :: t2) ->
  tid_phase tid (t1 ++ (tid, lock_write_item) :: t2) < 6 ->
  tid <> tid' ->
  In (tid', read_item v) t2 ->
  ~ In (tid', validate_read_item v) t1.
Proof.
  induction t1; intros T P N I.
  intros F; destruct F.
  rewrite <- app_comm_cons in *.
  destruct a; inversion T.
  all: intros F.
  all: rewrite <- H in *; rewrite <- H0 in *; clear H H0.
  all: cbn in P; destruct (Nat.eq_dec tid tid0); try congruence.
  all: match goal with
       | [ H1: sto_trace ((?t1, _) :: _ ++ (?t2, _) :: _),
           H2: ?t2 = ?t1 |- _ ] =>
         let PO := fresh in
         rewrite <- H2 in *; clear H2;
           generalize (phase_increase_head_middle _ _ _ _ _ H1); intros PO;
             cbn in PO; try omega
       | _ => idtac
       end.
  all: destruct F as [F | F]; [ try congruence | ].
  all: try solve [revert F; apply IHt1; auto; try omega].
  generalize (trace_after_lock _ _ _ H5); intros X.
  destruct X as [X | [X | X]].
  - assert (6 <= tid_phase tid (t1 ++ (tid, lock_write_item) :: t2)). {
      replace 6 with (action_phase unlock_write_item) by (now cbn).
      apply phase_increase_in; auto.
      apply in_or_app; now left.
    }
    omega.
  - apply (locked_by_other tid0) in X; auto.
    congruence.
    apply (trace_in_nonzero _ lock_write_item _ H5).
    apply in_or_app; right; now left.
  - rewrite H4 in *; clear H4.
    inversion F; clear F.
    rewrite H4 in *; clear vers H4.
    assert (v <= write_version t2). {
      apply read_version_increase_in with (tid0:=tid').
      apply sto_trace_app in H5; now apply sto_trace_cons in H5.
      auto.
    }
    omega.
Qed.
  
Lemma committable_unconflicted t:
  sto_trace t ->
  (exists t2, sto_trace (t2 ++ t) /\ all_committed (t2 ++ t)) ->
  trace_unconflicted t.
Proof.
  intros T; induction T; intros NU; destruct NU as [t2 [NU1 NU2]].
  1: constructor.
  Local Ltac myexists :=
    match goal with
    | [ IHT: ?a -> trace_unconflicted ?t1,
        H: sto_trace (?t2 ++ ?p :: ?t1) |- _ ] =>
      apply IHT; exists (t2 ++ [p]); rewrite <- app_assoc; cbn; split; auto
    end.
  all: try solve [apply internal_unc; [| cbn]; auto; myexists].
  - apply read_unc; auto; myexists.
  - apply lock_unc; [ myexists | ].
    remember (t2 ++ (tid0, lock_write_item) :: t) as tb.
    intros tid; destruct (Nat.eq_dec tid0 tid); [ now left | right ].
    intros F; destruct F as [vers [ER ENV]].
    assert (tid_phase tid tb = 4) as TP4X by (apply NU2).
    assert (In (tid, read_item vers) tb) as ERX. {
      rewrite Heqtb; apply in_or_app; right; now right.
    }
    generalize (committed_read_validated _ _ _ NU1 TP4X ERX); intros EVXB.
    assert (In (tid, validate_read_item vers) t2) as EVX. {
      rewrite Heqtb in EVXB; apply in_app_or in EVXB.
      destruct or EVXB; auto.
      destruct EVXB; [ congruence | contradiction ].
    }
    clear TP4X ENV EVXB.
    rewrite Heqtb in NU1;
      apply nonaborted_read_validate_different with (tid':=tid) (v:=vers) in NU1.
    contradiction.
    assert (tid_phase tid0 tb = 4) as TP4 by (apply NU2).
    unfold Top.tid in *; rewrite <- Heqtb; omega.
    auto.
    auto.
  - apply validate_read_unc; auto; myexists.
  - apply unlock_unc; auto; myexists.
  - apply complete_unc; auto; myexists.
Qed.

Lemma swap_forward_unconflicted tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  trace_unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
  action_phase a1 < 3 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros T U AP N.
  assert (tid1 > 0) as TZ1. {
    apply (trace_in_nonzero _ a1 _ T); right; now left.
  }
  assert (tid2 > 0) as TZ2. {
    apply (trace_in_nonzero _ a2 _ T); now left.
  }
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  assert (sto_trace ((tid1, a1) :: t)) as T1
      by (now apply (sto_trace_cons _ _ T)).
  destruct a1; cbn in AP; try omega.
  all: inversion T1.

  1, 3, 4: apply trace_swap_internal_forward; cbn; auto.

  - replace (write_version t) with (write_version ((tid2, a2) :: t)).
    constructor.
    now rewrite TP1.
    destruct a2; cbn; auto.
    inversion U.
    simpl in H9; contradiction.
    generalize (H8 tid1); intros X; destruct X as [X | X].
    congruence.
    contradict X.
    apply trace_outstanding_read_head; auto.

    destruct a2; inversion T.
    all: try constructor; fix_phase; auto.
    cbn; constructor; fix_phase; auto.
    intros vv I.
    assert (In (tid2, write_item vv) ((tid1, read_item v) :: t)) as II by (now right).
    apply (H8 vv) in II; destruct II; [ congruence | assumption ].
    intros vers I.
    assert (In (tid2, read_item vers) ((tid1, read_item v) :: t)) as II by (now right).
    apply (H8 vers) in II; destruct II; [ congruence | assumption ].
    rewrite H7, H1 in *; clear H7 H1.
    cbn in *.
    apply complete_write_item_step with (val:=val); fix_phase; auto.
    destruct (Nat.eq_dec tid2 tid1); [ congruence | assumption ].
    destruct (Nat.eq_dec tid2 tid1); assumption.

    destruct a2; cbn; auto.
    inversion T.
    simpl in H9; omega.

  - apply lock_write_item_step with (v:=v).
    now rewrite TP1.
    now right.
    cbn; destruct a2; auto.
    inversion T; simpl in H9.
    omega.
    destruct a2; inversion T.
    all: try solve [ cbn in *; contradiction ].
    all: try constructor; fix_phase; auto.
    cbn in H9; rewrite H9 in *; omega.
    intros vv I.
    assert (In (tid2, write_item vv) ((tid1, lock_write_item) :: t)) as II by (now right).
    apply (H8 vv) in II; destruct II; [ congruence | assumption ].
    intros vers I.
    assert (In (tid2, read_item vers) ((tid1, lock_write_item) :: t)) as II by (now right).
    apply (H8 vers) in II; destruct II; [ congruence | assumption ].
    omega.
Qed.

Lemma swap_committing tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  trace_unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
  3 <= action_phase a2 ->
  action_phase a2 <= 4 ->
  tid1 <> tid2 ->
  (a1 <> seq_point \/ a2 <> seq_point) ->
  sto_trace ((tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros T U AP2 AP2B N NS.
  assert (tid1 > 0) as TZ1. {
    apply (trace_in_nonzero _ a1 _ T); right; now left.
  }
  assert (tid2 > 0) as TZ2. {
    apply (trace_in_nonzero _ a2 _ T); now left.
  }
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  assert (sto_trace ((tid1, a1) :: t)) as T1
      by (now apply (sto_trace_cons _ _ T)).
  inversion T1; rewrite <- H0 in *; clear H0.
  all: try solve [apply trace_swap_internal_forward; cbn; auto].
  all: destruct a2; cbn in AP2; cbn in AP2B; try omega.
  all: clear AP1 AP1B.
  destruct or NS; contradiction.
  all: clear NS.
  all: try solve [apply trace_swap_internal_forward; cbn; auto].
  all: inversion T.

  admit.
  - replace (write_version t) with (write_version ((tid2, seq_point) :: t))
      by (now cbn).
    apply complete_write_item_step with (val:=val).
    now rewrite TP1.
    now cbn.
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
    constructor; auto.
    now rewrite <- TP2.
    admit.
  - simpl in H10.
    replace (write_version t) with (write_version ((tid2, validate_read_item v0) :: t))
      by (now cbn).
    apply complete_write_item_step with (val:=val).
    now rewrite TP1.
    now cbn.
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
    constructor; auto.
    now rewrite <- TP2.
    
    admit.
    inversion T.
    1, 3, 4: apply trace_swap_internal_forward; cbn; auto.

  - replace (write_version t) with (write_version ((tid2, a2) :: t)).
    constructor.
    now rewrite TP1.
    destruct a2; cbn; auto.
    inversion U.
    simpl in H9; contradiction.
    generalize (H8 tid1); intros X; destruct X as [X | X].
    congruence.
    contradict X.
    apply trace_outstanding_read_head; auto.

    destruct a2; inversion T.
    all: try constructor; fix_phase; auto.
    cbn; constructor; fix_phase; auto.
    intros vv I.
    assert (In (tid2, write_item vv) ((tid1, read_item v) :: t)) as II by (now right).
    apply (H8 vv) in II; destruct II; [ congruence | assumption ].
    intros vers I.
    assert (In (tid2, read_item vers) ((tid1, read_item v) :: t)) as II by (now right).
    apply (H8 vers) in II; destruct II; [ congruence | assumption ].
    rewrite H7, H1 in *; clear H7 H1.
    cbn in *.
    apply complete_write_item_step with (val:=val); fix_phase; auto.
    destruct (Nat.eq_dec tid2 tid1); [ congruence | assumption ].
    destruct (Nat.eq_dec tid2 tid1); assumption.

    destruct a2; cbn; auto.
    inversion T.
    simpl in H9; omega.

  - apply lock_write_item_step with (v:=v).
    now rewrite TP1.
    now right.
    cbn; destruct a2; auto.
    inversion T; simpl in H9.
    omega.
    destruct a2; inversion T.
    all: try solve [ cbn in *; contradiction ].
    all: try constructor; fix_phase; auto.
    cbn in H9; rewrite H9 in *; omega.
    intros vv I.
    assert (In (tid2, write_item vv) ((tid1, lock_write_item) :: t)) as II by (now right).
    apply (H8 vv) in II; destruct II; [ congruence | assumption ].
    intros vers I.
    assert (In (tid2, read_item vers) ((tid1, lock_write_item) :: t)) as II by (now right).
    apply (H8 vers) in II; destruct II; [ congruence | assumption ].
    omega.
Qed.

Fixpoint tid_phase_by_max tid (t:trace) :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then Nat.max (action_phase a) (tid_phase_by_max tid t')
    else tid_phase_by_max tid t'
  | [] => 0
  end.

Lemma tid_phase_max tid t:
  sto_trace t ->
  tid_phase tid t = tid_phase_by_max tid t.
Proof.
  induction t; intros T.
  cbn; auto.
  destruct a; cbn.
  rewrite <- (IHt (sto_trace_cons _ _ T)).
  destruct (Nat.eq_dec tid t0).
  assert (tid_phase tid t <= action_phase a). {
    apply phase_increase_head; now rewrite e.
  }
  now rewrite Max.max_l.
  auto.
Qed.
  
Lemma tid_phase_permutation tid t1 t2:
  Permutation t1 t2 ->
  sto_trace t1 ->
  sto_trace t2 ->
  tid_phase tid t1 = tid_phase tid t2.
Proof.
  intros P T1 T2.
  rewrite (tid_phase_max _ _ T1).
  rewrite (tid_phase_max _ _ T2).
  clear T1 T2; induction P; auto.
  destruct x; cbn; rewrite IHP; auto.
  destruct x; destruct y; cbn.
  destruct (Nat.eq_dec tid t0); destruct (Nat.eq_dec tid t); auto.
  rewrite Nat.max_assoc; rewrite (Nat.max_comm (action_phase a0));
    rewrite <- Nat.max_assoc; auto.
  congruence.
Qed.

Definition serial_permutation t1 t2 :=
  Permutation t1 t2
  /\ locked_by t1 0 = locked_by t2 0
  /\ write_version t1 = write_version t2
  /\ forall tid, trace_tid_last_write tid t1 = trace_tid_last_write tid t2.

Lemma serial_permutation_cons t1 t2 a:
  serial_permutation t1 t2 ->
  serial_permutation (a :: t1) (a :: t2).
Proof.
  intros S; destruct S as [P [L [WV LW]]].
  split; [ | split; [ | split ]].
  now apply perm_skip.
  destruct a; destruct a; now cbn.
  destruct a; destruct a; now cbn.
  intros tid; destruct a; destruct a; cbn.
  all: destruct (Nat.eq_dec tid t); auto.
Qed.

Lemma serial_permutation_app t1 t2 th:
  serial_permutation t1 t2 ->
  serial_permutation (th ++ t1) (th ++ t2).
Proof.
  induction th; intros S; cbn; auto.
  apply serial_permutation_cons; auto.
Qed.

Lemma sto_trace_permutation_cons t1 t2 tid a:
  sto_trace ((tid, a) :: t1) ->
  sto_trace t2 ->
  serial_permutation t1 t2 ->
  sto_trace ((tid, a) :: t2).
Proof.
  intros T1X T2 S.
  unfold serial_permutation in S.
  destruct S as [P [L [WV LW]]].
  assert (sto_trace t1) as T1 by (apply (sto_trace_cons _ _ T1X)).
  assert (tid_phase tid t1 = tid_phase tid t2) as PE by (now apply tid_phase_permutation).
  inversion T1X; rewrite <- H0 in *; clear H0.

  - constructor; try rewrite <- PE; auto.
  - rewrite WV; constructor; try rewrite <- PE; auto.
    now rewrite <- L.
  - constructor; try rewrite <- PE; auto.
  - constructor; try rewrite <- PE; auto.
  - apply lock_write_item_step with (v:=v); try rewrite <- PE; auto.
    apply Permutation_in with (l:=t1); auto.
    now rewrite <- L.
  - constructor; try rewrite <- PE; auto.
    intros vv I.
    apply Permutation_in with (l:=t1); auto.
    apply (H3 vv).
    apply Permutation_in with (l:=t2); auto.
    now apply Permutation_sym.
  - constructor; try rewrite <- PE; auto.
    apply locked_by_self_or in H3.
    destruct or H3.
    rewrite L in H3; apply locked_by_unlocked; auto.
    rewrite L in H3; apply locked_by_self; auto.
    now rewrite <- WV.
  - constructor; try rewrite <- PE; auto.
  - constructor; try rewrite <- PE; auto.
    now rewrite <- L.
  - constructor; try rewrite <- PE; auto.
    intros vv I.
    apply Permutation_in with (l:=t1); auto.
    apply H3.
    apply Permutation_in with (l:=t2); auto.
    now apply Permutation_sym.
  - rewrite WV.
    apply complete_write_item_step with (val:=val); try rewrite <- PE; auto.
    now rewrite <- L.
    now rewrite <- LW.
  - constructor; try rewrite <- PE; auto.
    now rewrite <- L.
    contradict H4.
    apply Permutation_in with (l:=t2); auto.
    now apply Permutation_sym.
Qed.

Lemma sto_trace_permutation_app t1 t2 th:
  sto_trace (th ++ t1) ->
  sto_trace t2 ->
  serial_permutation t1 t2 ->
  sto_trace (th ++ t2).
Proof.
  induction th; intros T1X T2 S.
  simpl; auto.
  rewrite <- app_comm_cons in *.
  assert (serial_permutation (th ++ t1) (th ++ t2)) by
      (now apply serial_permutation_app).
  destruct a.
  apply sto_trace_permutation_cons with (t1 := th ++ t1); auto.
  apply IHth; auto.
  apply (sto_trace_cons _ _ T1X).
Qed.

Lemma serial_permutation_unconflicted tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  trace_unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
  action_phase a1 < 3 ->
  tid1 <> tid2 ->
  serial_permutation ((tid2, a2) :: (tid1, a1) :: t)
                     ((tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros T U AP N.
  assert (tid1 > 0) as TZ1. {
    apply (trace_in_nonzero _ a1 _ T); right; now left.
  }
  assert (tid2 > 0) as TZ2. {
    apply (trace_in_nonzero _ a2 _ T); now left.
  }
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }
  split; [ | split; [ | split ]].
  - constructor.
  - cbn; destruct a1; destruct a2; try congruence.
    all: inversion T; cbn in *; try congruence; omega.
  - cbn; destruct a1; destruct a2; try congruence.
    all: inversion T; cbn in *; try congruence; omega.
  - intros tid; cbn.
    destruct (Nat.eq_dec tid tid1); destruct (Nat.eq_dec tid tid2);
      congruence.
Qed.

Lemma swap_forward_all_committed tid1 tid2 a1 a2 t1 t2:
  sto_trace (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) ->
  all_committed (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) ->
  action_phase a1 < 3 ->
  tid1 <> tid2 ->
  sto_trace (t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
Proof.
  intros T1 A AP N.
  generalize (sto_trace_app _ _ T1); intros TB.
  assert (trace_unconflicted ((tid2, a2) :: (tid1, a1) :: t2)). {
    apply committable_unconflicted; auto.
    now exists t1.
  }
  apply sto_trace_permutation_app with (t1:=(tid2,a2)::(tid1,a1)::t2).
  auto.
  apply swap_forward_unconflicted; auto.
  apply serial_permutation_unconflicted; auto.
Qed.

Function swap_forward_once (t:trace) { measure length t } :=
  match t with
  | (tid2, a2) :: (tid1, a1) :: t' =>
    if Nat.eq_dec tid2 tid1
    then (tid2, a2) :: swap_forward_once ((tid1, a1) :: t')
    else if action_phase a1 <? 3
         then (tid1, a1) :: (tid2, a2) :: t'
         else (tid2, a2) :: swap_forward_once ((tid1, a1) :: t')
  | _ => t
  end.
Proof.
  all: intros; cbn; apply lt_n_S; omega.
Defined.

Lemma swap_forward_once_result t:
  swap_forward_once t = t
  \/ (exists t1 t2 tid1 tid2 a1 a2,
         t = t1 ++ (tid2, a2) :: (tid1, a1) :: t2
         /\ tid1 <> tid2
         /\ action_phase a1 < 3
         /\ swap_forward_once t = t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
Proof.
  functional induction (swap_forward_once t); cbn; auto.
  - destruct IHt0.
    left; now rewrite H.
    destruct H as [t1 [t2 [tid1 [tid3 [a4 [a3 H]]]]]].
    right.
    exists ((tid2, a2) :: t1), t2, tid1, tid3, a4, a3.
    intuition.
    now rewrite H0.
    now rewrite H3.
  - right.
    exists [], t', tid1, tid2, a1, a2.
    intuition.
    now rewrite <- Nat.ltb_lt.
  - destruct IHt0.
    left; now rewrite H.
    destruct H as [t1 [t2 [tid0 [tid3 [a4 [a3 H]]]]]].
    right.
    exists ((tid2, a2) :: t1), t2, tid0, tid3, a4, a3.
    intuition.
    now rewrite H0.
    now rewrite H3.
Qed.
  
Lemma swap_forward_once_correct t:
  sto_trace t ->
  all_committed t ->
  sto_trace (swap_forward_once t).
Proof.
  intros T A.
  destruct (swap_forward_once_result t).
  now rewrite H.
  destruct H as [t1 [t2 [tid1 [tid2 [a1 [a2 [H [N [AP S]]]]]]]]].
  rewrite S.
  rewrite H in *.
  apply swap_forward_all_committed; auto.
Qed.

Inductive serial_trace : trace -> Prop :=
| serial_empty : serial_trace []
| serial_singleton : forall tid a,
    serial_trace [(tid, a)]
| serial_same: forall tid a1 a2 t,
    serial_trace ((tid, a2) :: t) ->
    serial_trace ((tid, a1) :: (tid, a2) :: t)
| serial_change: forall tid1 tid2 a1 a2 t,
    serial_trace ((tid2, a2) :: t) ->
    tid_phase tid1 ((tid2, a2) :: t) = 0 ->
    serial_trace ((tid1, a1) :: (tid2, a2) :: t).

Lemma swap_forward_once_fixpoint_contents t:
  swap_forward_once t = t ->
  forall t1 tid1 tid2 a1 a2 t2,
    t = t1 ++ (tid2, a2) :: (tid1, a1) :: t2 ->
    tid1 = tid2 \/ 3 <= action_phase a1.
Proof.
  functional induction (swap_forward_once t).
  all: intros S.
  - inversion S; rewrite H0; intros.
    destruct t1; cbn in *; inversion H.
    now left.
    apply (IHt0 H0 t1 tid1 tid0 a0 a3 t2); auto.
  - inversion S; subst.
    destruct (Nat.eq_dec tid2 tid2); congruence.
  - inversion S; rewrite H0; intros.
    destruct t1; cbn in *; inversion H.
    right.
    rewrite leb_iff_conv in e1; rewrite <- H5; omega.
    apply (IHt0 H0 t1 tid0 tid3 a0 a3 t2); auto.
  - intros.
    destruct t.
    destruct t1; discriminate.
    destruct t.
    destruct t1; inversion H; destruct t1; discriminate.
    destruct p; destruct p0; contradiction.
Qed.

(* the following is not true *)
Lemma swap_forward_once_fixpoint_serial t:
  sto_trace t ->
  (exists t2, all_committed (t2 ++ t)) ->
  swap_forward_once t = t ->
  serial_trace t.
Proof.
  induction t; intros T E S.
  constructor.
  assert (serial_trace t). {
    apply IHt.
    apply (sto_trace_cons _ _ T).
    destruct E as [t2 E].
    exists (t2 ++ [a]); rewrite <- app_assoc; simpl; auto.
    destruct a; destruct t; rewrite swap_forward_once_equation in S.
    cbn; auto.
    destruct p.
    destruct (Nat.eq_dec t0 t1).
    inversion S; rewrite H0; auto.
    remember (action_phase a0 <? 3) as A; destruct A.
    inversion S; subst; contradiction.
    inversion S; rewrite H0; auto.
  }
  generalize (swap_forward_once_fixpoint_contents _ S); intros X.
  destruct t.
  destruct a; apply serial_singleton.
  destruct a; destruct p.
  generalize (X [] t1 t0 a0 a t).
  intros Y; cbn in Y.
  assert (t1 = t0 \/ 3 <= action_phase a0). {
    apply Y; auto.
  }
  destruct H0.
  rewrite <- H0; now constructor.
  apply serial_change; auto.
  assert (forall a, ~ In (t0, a) t). {
    intros aa I.
    admit.
  }
  
  contradict X.
    apply eq_refl in Y.
  functional induction (swap_forward_once t).
  all: intros T E S.
  - apply serial_same.
    apply IHt0.
    apply (sto_trace_cons _ _ T).
    destruct E as [t2 E].
    exists (t2 ++ [(tid2, a2)]); rewrite <- app_assoc; now cbn.
    inversion S; now rewrite H0.
  - inversion S; subst.
    destruct (Nat.eq_dec tid2 tid2); congruence.
  - apply serial_change.
    apply IHt0.
    apply (sto_trace_cons _ _ T).
    destruct E as [t2 E].
    exists (t2 ++ [(tid2, a2)]); rewrite <- app_assoc; now cbn.
    inversion S; now rewrite H0.
    
    admit.
  - destruct t; try constructor.
    destruct p; destruct t; try constructor.
    destruct p; contradiction.
Admitted.
