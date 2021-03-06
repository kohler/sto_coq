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
Definition addr := nat.


Ltac myauto :=
  repeat match goal with
  | |- context[_] =>
      auto 100; intuition; cbn in *; simpl in *; auto 100
  | |- context[_] =>
      try contradiction; try discriminate
end.


Inductive action:=
| start_txn : action
| read_item : forall (ad:addr) (vers:version), action
| write_item : forall (ad:addr) (val:value), action
| try_commit_txn : action
| lock_write_item : forall (ad:addr), action
| seq_point : action
| validate_read_item : forall (ad:addr) (vers:version), action
| abort_txn : action
| unlock_write_item : forall (ad:addr), action
| commit_txn : action
| complete_write_item : forall (ad:addr) (vers:version), action
| commit_done_txn : action.
(*sp later than last lock, but must before the first commit*)

Lemma action_dec (a b:action):
  { a = b } + { a <> b }.
Proof.
  decide equality.
  all: apply Nat.eq_dec.
Qed.


Definition trace := list (tid * action).

(* Return the “phase” of an action. *)
Definition action_phase (a:action) :=
  match a with
  | start_txn => 1
  | read_item _ _ => 1
  | write_item _ _ => 1
  | try_commit_txn => 2
  | lock_write_item _ => 2
  | seq_point => 3
  | validate_read_item _ _ => 3
  | commit_txn => 4
  | complete_write_item _ _ => 4
  | commit_done_txn => 4
  | abort_txn => 6
  | unlock_write_item _ => 6
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

Lemma tid_phase_in tid t n:
  tid_phase tid t = n ->
  n > 0 ->
  exists a, In (tid, a) t /\ action_phase a = n.
Proof.
  induction t; intros; cbn in H.
  omega.
  destruct a as [tid' a]; destruct (Nat.eq_dec tid tid').
  rewrite e; exists a; intuition.
  generalize (IHt H H0); intros X; destruct X as [a0 [I P]].
  exists a0; intuition.
Qed.

Lemma tid_phase_split tid t n:
  tid_phase tid t = n ->
  n > 0 ->
  exists t1 a t2, t = t1 ++ (tid, a) :: t2
                  /\ action_phase a = n
                  /\ tid_phase tid t1 = 0.
Proof.
  induction t; intros; cbn in H.
  omega.
  destruct a as [tid' a]; destruct (Nat.eq_dec tid tid').
  rewrite e; exists [], a, t; intuition.
  generalize (IHt H H0); intros X.
  destruct X as [t1 [a0 [t2 [P1 [P2 P3]]]]].
  exists ((tid', a) :: t1), a0, t2.
  cbn; rewrite P1.
  destruct (Nat.eq_dec tid tid'); [ congruence | ].
  intuition.
Qed.

Lemma tid_phase_zero_app_skip tid t1 t2:
  tid_phase tid t1 = 0 ->
  tid_phase tid (t1 ++ t2) = tid_phase tid t2.
Proof.
  induction t1; cbn; auto.
  intros H; destruct a as [tid2 a2].
  destruct (Nat.eq_dec tid tid2).
  destruct a2; cbn in H; omega.
  now apply IHt1.
Qed.

Lemma tid_phase_not_in_zero tid t:
  (forall a, ~ In (tid, a) t) ->
  tid_phase tid t = 0.
Proof.
  induction t; intros F; cbn; auto.
  destruct a as [tid' a]; destruct (Nat.eq_dec tid tid').
  generalize (F a); intros FF; cbn in FF.
  rewrite e in FF.
  contradict FF; now left.
  apply IHt; intros aa I.
  apply (F aa); now right.
Qed.

Lemma tid_phase_zero_not_in tid t:
  tid_phase tid t = 0 ->
  forall a, ~ In (tid, a) t.
Proof.
  induction t; intros P aa I.
  destruct I.
  destruct a; cbn in P.
  destruct (Nat.eq_dec tid n); [ destruct a; cbn in P; omega | ].
  destruct I as [I|I]; [ inversion I; congruence | ].
  now apply (IHt P aa).
Qed.

Lemma tid_phase_zero_app tid t1 t2:
  tid_phase tid (t1 ++ t2) = 0 ->
  tid_phase tid t1 = 0.
Proof.
  induction t1; cbn; auto.
  destruct a as [tid2 a2]; destruct (Nat.eq_dec tid tid2); auto.
Qed.

Lemma tid_phase_zero_cons tid x t:
  tid_phase tid (x :: t) = 0 ->
  tid_phase tid t = 0.
Proof.
  intros; destruct x; cbn in *.
  destruct (Nat.eq_dec tid n); auto.
  destruct a; cbn in H; omega.
Qed.


(* Return the version number of the last committed write *)
Fixpoint write_version (a:addr) (t:trace): version :=
  match t with
  | (_, complete_write_item a' v) :: t' =>
    if Nat.eq_dec a a' then v else write_version a t'
  | _ :: t' => write_version a t'
  | [] => 0
  end.

Fixpoint tid_last_write tid a t: option value :=
  match t with
  | (tid', ac) :: t' =>
    if Nat.eq_dec tid tid' 
    then match ac with
         | write_item a' v =>
           if Nat.eq_dec a a' then Some v else tid_last_write tid a t'
         | complete_write_item a' _ =>
           if Nat.eq_dec a a' then None else tid_last_write tid a t'
         | _ => tid_last_write tid a t'
         end
    else tid_last_write tid a t'
  | [] => None
  end.

Fixpoint locked_by (a:addr) (t:trace) default : tid :=
  match t with
  | (tid, lock_write_item a') :: t' =>
    if Nat.eq_dec a a' then tid else locked_by a t' default
  | (_, unlock_write_item a') :: t' =>
    if Nat.eq_dec a a' then default else locked_by a t' default
  | (_, complete_write_item a' _) :: t' =>
    if Nat.eq_dec a a' then default else locked_by a t' default
  | _ :: t' => locked_by a t' default
  | [] => default
  end.

Inductive sto_trace : trace -> Prop :=

| empty_step : sto_trace []

| start_txn_step: forall t tid,
    tid_phase tid t = 0
    -> tid > 0
    -> sto_trace t
    -> sto_trace ((tid, start_txn)::t)

| read_item_step: forall tid t ad,
    tid_phase tid t = 1
    -> locked_by ad t 0 = 0
    -> sto_trace t
    -> sto_trace ((tid, read_item ad (write_version ad t)) :: t)

| write_item_step: forall tid t ad val,
    tid_phase tid t = 1
    -> sto_trace t
    -> sto_trace ((tid, write_item ad val) :: t)

| try_commit_txn_step: forall tid t,
    tid_phase tid t = 1
    -> sto_trace t
    -> sto_trace ((tid, try_commit_txn)::t)

| lock_write_item_step: forall tid t ad v,
    tid_phase tid t = 2
    -> In (tid, write_item ad v) t
    -> locked_by ad t 0 = 0
    -> sto_trace t
    -> sto_trace ((tid, lock_write_item ad) :: t)

(*sequential point*)
| seq_point_step: forall tid t,
    tid_phase tid t = 2
    -> (forall ad v, In (tid, write_item ad v) t
                     -> In (tid, lock_write_item ad) t)
    -> sto_trace t
    -> sto_trace ((tid, seq_point) :: t)

| validate_read_item_step: forall tid t ad vers,
    tid_phase tid t = 3
    -> locked_by ad t tid = tid (* unlocked or locked by me *)
    -> write_version ad t = vers
    -> In (tid, read_item ad vers) t (* only validate unvalidated reads we performed *)
    -> ~ In (tid, validate_read_item ad vers) t
    -> sto_trace t
    -> sto_trace ((tid, validate_read_item ad vers) :: t)

| abort_txn_step: forall tid t,
    tid_phase tid t > 0
    -> tid_phase tid t < 4
    -> sto_trace t
    -> sto_trace ((tid, abort_txn) :: t)

| unlock_item_step: forall tid t ad,
    tid_phase tid t = 6
    -> locked_by ad t 0 = tid
    -> sto_trace t
    -> sto_trace ((tid, unlock_write_item ad) :: t)

| commit_txn_step: forall tid t,
    tid_phase tid t = 3
    -> (forall ad vers, In (tid, read_item ad vers) t
                        -> In (tid, validate_read_item ad vers) t)
    -> sto_trace t
    -> sto_trace ((tid, commit_txn) :: t)

| complete_write_item_step: forall tid t ad val,
    tid_phase tid t = 4
    -> locked_by ad t 0 = tid
    -> tid_last_write tid ad t = Some val
    -> sto_trace t
    -> sto_trace ((tid, complete_write_item ad (S (write_version ad t))) :: t)

| commit_done_step: forall tid t,
    tid_phase tid t = 4
    -> (forall ad, locked_by ad t 0 <> tid)
    -> ~ In (tid, commit_done_txn) t
    -> sto_trace t
    -> sto_trace ((tid, commit_done_txn) :: t).
Hint Constructors sto_trace.


(** Facts about traces *)

Lemma trace_cons ta t:
  sto_trace (ta :: t) -> sto_trace t.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma trace_app t1 t2:
  sto_trace (t1 ++ t2) -> sto_trace t2.
Proof.
  intros.
  induction t1. rewrite app_nil_l in H. auto.
  apply IHt1.
  now apply trace_cons with (ta:=a).
Qed.



(** Facts about how phases change *)

Lemma phase_increase_head tid a t:
  sto_trace ((tid, a) :: t) ->
  tid_phase tid t <= action_phase a.
Proof.
  intros; inversion H; cbn; omega.
Qed.

Lemma phase_increase_app tid t1 t2:
  sto_trace (t1 ++ t2) ->
  tid_phase tid t2 <= tid_phase tid (t1 ++ t2).
Proof.
  induction t1; intros.
  - simpl; omega.
  - rewrite <- app_comm_cons in H; destruct a.
    assert (sto_trace (t1 ++ t2)) by (now apply trace_cons in H).
    apply IHt1 in H0.
    simpl; destruct (Nat.eq_dec tid t).
    + subst; apply phase_increase_head in H; omega.
    + auto.
Qed.

Lemma phase_increase_in tid a t:
  sto_trace t ->
  In (tid, a) t ->
  action_phase a <= tid_phase tid t.
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
  tid_phase tid t2 < action_phase a ->
  In (tid, a) t1.
Proof.
  intros T I A.
  apply in_app_or in I; destruct I as [I | I]; auto.
  apply trace_app in T.
  apply (phase_increase_in _ _ _ T) in I.
  omega.
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


Lemma at_most_one_seq_point tid t:
  sto_trace ((tid, seq_point) :: t) ->
  ~ In (tid, seq_point) t.
Proof.
  intros H F.
  apply (phase_increase_in _ _ _ (trace_cons _ _ H)) in F.
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
    destruct I; [ | now apply (IHt _ _ (trace_cons _ _ H)) in H0 ].
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

Lemma trace_no_dummy tid a t:
  sto_trace t ->
  In (tid, a) t ->
  action_phase a > 0.
Proof.
  induction t; intros T I; destruct I.
  rewrite H in T; inversion T; cbn; omega.
  apply IHt; auto.
  now apply trace_cons in T.
Qed.



(** Facts about versions *)

Lemma write_version_increase_app ad t1 t2:
  sto_trace (t1 ++ t2) ->
  write_version ad t2 <= write_version ad (t1 ++ t2).
Proof.
  induction t1; intros T.
  cbn; omega.
  destruct a; inversion T; rewrite <- H0 in *; clear H0.
  all: cbn; auto.
  destruct (Nat.eq_dec ad ad0); auto.
  rewrite <- e in *; clear e; auto.
Qed.

Lemma read_version_increase_in tid ad v t:
  sto_trace t ->
  In (tid, read_item ad v) t ->
  v <= write_version ad t.
Proof.
  intros T; induction T; intros I.
  destruct I.
  all: destruct I as [I|I]; try congruence.
  all: cbn; auto.
  inversion I; omega.
  destruct (Nat.eq_dec ad ad0); auto.
  rewrite <- e in *; clear e; auto.
Qed.


(** Facts about [remove_tid] *)

Fixpoint filter_tid tid (t:trace) :=
  match t with
  | (tid', a) :: t' => if Nat.eq_dec tid tid'
                       then (tid', a) :: filter_tid tid t'
                       else filter_tid tid t'
  | [] => []
  end.

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

Lemma remove_tid_write_version tid ad t:
  sto_trace t ->
  tid_phase tid t <> 4 ->
  write_version ad (remove_tid tid t) = write_version ad t.
Proof.
  intros T; induction T; intros P; cbn in *; auto.
  all: destruct (Nat.eq_dec tid tid0); [ rewrite e in *; clear e | ].
  all: try solve [ apply IHT; omega ].
  contradiction.
  cbn; destruct (Nat.eq_dec ad ad0); auto.
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

Lemma remove_tid_last_write tid tid' ad t:
  tid <> tid' ->
  tid_last_write tid' ad (remove_tid tid t) = tid_last_write tid' ad t.
Proof.
  induction t; intros N; cbn in *; auto.
  destruct a; destruct a;
    destruct (Nat.eq_dec tid' t0); destruct (Nat.eq_dec tid t0);
      cbn; auto.
  all: try congruence.
  all: destruct (Nat.eq_dec tid' t0); try congruence; auto.
  all: destruct (Nat.eq_dec ad ad0); auto.
Qed.


(** Facts about [locked_by] *)

Lemma locked_by_unlocked_in tid ad t:
  (forall x, In x t -> fst x > 0) ->
  locked_by ad t 0 = 0 ->
  locked_by ad t tid = tid.
Proof.
  induction t; intros A L; cbn in *; auto.
  destruct a; destruct a.
  all: try solve [ apply IHt; auto ].
  all: destruct (Nat.eq_dec ad ad0); auto.
  rewrite <- e in *; clear e.
  assert (n > 0). {
    replace n with (fst (n, lock_write_item ad)).
    apply A; now left.
    now simpl.
  }
  omega.
Qed.

Lemma locked_by_unlocked tid ad t:
  sto_trace t ->
  locked_by ad t 0 = 0 ->
  locked_by ad t tid = tid.
Proof.
  intros T L; apply locked_by_unlocked_in; auto.
  intros x I; destruct x; simpl.
  now apply (trace_in_nonzero _ a t).
Qed.

Lemma locked_by_self tid ad t:
  sto_trace t ->
  locked_by ad t 0 = tid ->
  locked_by ad t tid = tid.
Proof.
  intros T; induction T; cbn in *; intros L; auto.
  all: destruct (Nat.eq_dec ad ad0); auto.
Qed.

Lemma locked_by_self_or tid ad t:
  locked_by ad t tid = tid ->
  locked_by ad t 0 = 0 \/ locked_by ad t 0 = tid.
Proof.
  induction t; cbn in *; intros.
  now left.
  destruct a; destruct a; try solve [ now apply IHt ].
  all: destruct (Nat.eq_dec ad ad0); auto.
Qed.

Lemma locked_by_or tid tid' ad t:
  locked_by ad t tid = locked_by ad t tid' \/ locked_by ad t 0 = 0.
Proof.
  induction t; cbn in *; intros.
  now right.
  destruct a; destruct a; auto.
  all: destruct (Nat.eq_dec ad ad0); auto.
Qed.

Lemma locked_by_other tid tid' ad t:
  sto_trace t ->
  tid' > 0 ->
  locked_by ad t 0 = tid' ->
  locked_by ad t tid = tid'.
Proof.
  intros T; induction T; cbn in *; intros N L; auto.
  omega.
  all: destruct (Nat.eq_dec ad ad0); auto.
  all: omega.
Qed.

Lemma remove_tid_locked_by_neq tid tid' ad t:
  sto_trace t ->
  locked_by ad t tid <> tid ->
  locked_by ad (remove_tid tid t) tid' = locked_by ad t tid'.
Proof.
  intros T; induction T; intros L; cbn in *; auto.
  all: destruct (Nat.eq_dec tid tid0); auto.
  all: cbn; destruct (Nat.eq_dec ad ad0); auto.
  all: try congruence.
Qed.

Lemma remove_tid_locked_by_eq tid tid' ad t:
  sto_trace t ->
  locked_by ad t tid = tid ->
  locked_by ad (remove_tid tid t) tid' = tid'.
Proof.
  intros T; induction T; intros L; cbn in *; auto.
  all: destruct (Nat.eq_dec tid tid0); auto.
  all: cbn in *; destruct (Nat.eq_dec ad ad0); auto.
  apply IHT; apply locked_by_unlocked; auto.
  all: try congruence.
  all: apply IHT; apply locked_by_self; subst; auto.
Qed.



Definition all_committed (t:trace) :=
  forall tid,
    tid_phase tid t > 0 ->
    tid_phase tid t = 4.

Lemma in_all_committed tid a t:
  sto_trace t ->
  all_committed t ->
  In (tid, a) t ->
  action_phase a <= 4.
Proof.
  intros T A I.
  assert (tid_phase tid t > 0). {
    generalize I; intros II; apply phase_increase_in in I; auto.
    apply trace_no_dummy in II; auto.
    omega.
  }
  apply A in H.
  apply phase_increase_in in I; auto; omega.
Qed.



Lemma track_lock_cons tid tid' ad t a:
  sto_trace ((tid', a) :: t) ->
  locked_by ad t 0 = tid ->
  locked_by ad ((tid', a) :: t) 0 = tid
  \/ tid = 0 /\ a = lock_write_item ad
  \/ tid = tid' /\ a = unlock_write_item ad
  \/ tid = tid' /\ exists val, a = complete_write_item ad val.
Proof.
  intros T L.
  assert (tid' > 0) as TG. {
    apply trace_in_nonzero with (a:=a) (t:=(tid', a)::t); cbn; auto.
  }
  inversion T; subst; cbn; auto.
  all: destruct (Nat.eq_dec ad ad0); cbn; subst; auto.
  right; right; right; eauto.
Qed.

Lemma locked_phase tid ad t:
  sto_trace t ->
  locked_by ad t 0 = tid ->
  tid > 0 ->
  tid_phase tid t >= 2.
Proof.
  intros T; revert tid; induction T; intros tid L G.
  1: cbn in L; omega.
  all: cbn.
  all: destruct (Nat.eq_dec tid tid0); try omega.
  all: try (now apply IHT).
  1-3: subst; apply IHT in e; omega.
  1-3: cbn in L; destruct (Nat.eq_dec ad ad0); auto; omega.
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
  now apply trace_cons in H.
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
  now apply trace_cons in H.
Qed.


Lemma phase_2_preserves_lock tid ad t1 t2:
  sto_trace (t1 ++ t2) ->
  tid_phase tid (t1 ++ t2) = 2 ->
  locked_by ad t2 0 = tid ->
  locked_by ad (t1 ++ t2) 0 = tid.
Proof.
  revert t2.
  induction t1; intros t2 T P L.
  now cbn.
  destruct a as [tid' a].
  cbn in P; destruct (Nat.eq_dec tid tid').
  - rewrite <- e in *; clear tid' e.
    rewrite <- app_comm_cons in *.
    inversion T; rewrite <- H0 in P; cbn in P; try omega.
    apply locked_phase in L.
    assert (tid_phase tid t2 <= 1). {
      rewrite <- H1; apply phase_increase_app; auto.
    }
    omega.
    now apply trace_app in H3.
    apply trace_phase_nonzero with (t:=t1 ++ t2); auto; omega.
    cbn; destruct (Nat.eq_dec ad ad0); auto.
  - assert (locked_by ad (t1 ++ t2) 0 = tid) as LA. {
      apply IHt1; auto.
      now apply (trace_cons _ _ T).
    }
    assert (tid > 0). {
      apply trace_phase_nonzero with (t:=t1++t2).
      now apply (trace_cons _ _ T).
      omega.
    }
    all: cbn in *; inversion T; auto.
    all: destruct (Nat.eq_dec ad ad0); auto.
    all: rewrite <- e in *; clear ad0 e; rewrite LA in *; omega.
Qed.

Lemma locked_at_seq_point tid t1 t2 ad v:
  sto_trace ((tid, seq_point) :: t1 ++ (tid, write_item ad v) :: t2) ->
  locked_by ad (t1 ++ (tid, write_item ad v) :: t2) 0 = tid.
Proof.
  intros T.
  inversion T.
  assert (tid > 0) as TG. {
    apply trace_in_nonzero with (a:=write_item ad v) (t:=t); rewrite H0; auto.
    apply in_or_app; right; now left.
  }

  assert (In (tid, lock_write_item ad) t1). {
    assert (In (tid, lock_write_item ad) t). {
      rewrite H0.
      apply H2 with (v0:=v).
      apply in_or_app; cbn; intuition.
    }
    apply phase_increase_in_app with (t2:=(tid, write_item ad v) :: t2); auto.
    now rewrite <- H0.
    simpl; destruct (Nat.eq_dec tid tid); intuition.
  }

  apply in_split in H4.
  destruct H4 as [t1a [t1b T1]].
  subst.
  repeat rewrite <- app_assoc in *.
  repeat rewrite <- app_comm_cons in *.
  remember ((tid, lock_write_item ad) :: t1b ++ (tid, write_item ad v) :: t2) as tx.
  assert (locked_by ad tx 0 = tid). {
    rewrite Heqtx.
    cbn.
    destruct (Nat.eq_dec ad ad); congruence.
  }
  assert (tid_phase tid tx = 2). {
    assert (tid_phase tid tx >= 2). {
      apply locked_phase with (ad:=ad); auto.
      now apply trace_app with (t1:=t1a).
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
  -> (exists ad, action = complete_write_item ad (S (write_version ad t2)))
     \/ action = commit_done_txn.
Proof.
  intros T.
  assert (tid_phase tid (t1 ++ (tid, commit_txn) :: t2) = 4) as TG4. {
    apply trace_cons in T.
    apply commit_phase_app; auto.
    simpl; destruct (Nat.eq_dec tid tid); congruence.
  }
  inversion T; try omega.
  2: now right.
  left.

  exists ad.
  assert (write_version ad (t1 ++ (tid, commit_txn) :: t2) =
          write_version ad t2). {
    subst.
    clear TG4 val H2 H3 H4 H5.
    inversion T; subst.
    clear T H5 val H1.
    remember (t1 ++ (tid, commit_txn) :: t2) as t.
    revert t1 t2 tid Heqt H3 H4.
    induction H6; intros t1 t2 tid T P L.
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
      by (apply (trace_in_nonzero _ commit_txn _ H6);
          rewrite Teq; apply in_or_app; right; now left).
    all: try (destruct (Nat.eq_dec ad ad0); [ omega | ]).
    1,2,4,5: rewrite <- Teq; apply (IHsto_trace _ _ _ Teq); auto.
    all: rewrite <- e in *; clear tid0 e; auto.
    assert (action_phase commit_txn <= tid_phase tid t). {
      apply phase_increase_in; auto.
      rewrite Teq; apply in_or_app; right; now left.
    }
    cbn in H3; omega.
  }

  now rewrite H6.
Qed.

Lemma unlocked_after_commit_done tid ad t1 t2:
  sto_trace (t1 ++ (tid, commit_done_txn) :: t2) ->
  locked_by ad (t1 ++ (tid, commit_done_txn) :: t2) 0 <> tid.
Proof.
  intros T.
  assert (tid > 0) as G. {
    apply (trace_in_nonzero tid commit_done_txn _ T).
    apply in_or_app; right; now left.
  }
  induction t1; cbn in *.
  inversion T; auto.
  destruct a; destruct a.
  all: try solve [ apply IHt1; now apply trace_cons in T ].
  all: destruct (Nat.eq_dec ad ad0); auto.
  2,3,4: apply IHt1; apply (trace_cons _ _ T).
  inversion T.
  assert (4 <= tid_phase tid (t1 ++ (tid, commit_done_txn) :: t2)). {
    replace 4 with (action_phase commit_done_txn) by (now cbn).
    apply phase_increase_in; auto.
    apply in_or_app; right; now left.
  }
  intros F; rewrite <- F in *; omega.
Qed.

Lemma no_steps_after_commit_done tid tid' a t1 t2:
  sto_trace ((tid', a) :: t1 ++ (tid, commit_done_txn) :: t2) ->
  tid <> tid'.
Proof.
  intros T.
  assert (tid_phase tid (t1 ++ (tid, commit_done_txn) :: t2) = 4) as P4. {
    apply commit_phase_app.
    now apply trace_cons in T.
    cbn; destruct (Nat.eq_dec tid tid); congruence.
  }
  remember (t1 ++ (tid, commit_done_txn) :: t2) as t.
  inversion T; try congruence.
  all: destruct (Nat.eq_dec tid tid'); auto.
  all: rewrite <- e in *; clear e.
  - omega.
  - assert (locked_by ad t 0 <> tid). {
      rewrite Heqt in *; now apply unlocked_after_commit_done.
    }
    congruence.
  - assert (In (tid, commit_done_txn) t). {
      rewrite Heqt; apply in_or_app; right; now left.
    }
    contradiction.
Qed.


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
    rewrite <- (remove_tid_write_version _ _ _ T P); constructor.
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
    intros ad v I.
    apply in_remove_tid; auto.
    apply (H0 ad v).
    apply (remove_tid_in _ _ _ I).
    auto.
  }

  {
    constructor.
    rewrite (remove_tid_phase _ _ _ n); auto.
    destruct (Nat.eq_dec (locked_by ad t tid) tid);
      [ rewrite remove_tid_locked_by_eq | rewrite remove_tid_locked_by_neq ];
      auto.
    rewrite remove_tid_write_version; auto.
    auto.
    apply in_remove_tid; auto.
    contradict H3; now apply remove_tid_in in H3.
    auto.
  }

  {
    constructor.
    rewrite (remove_tid_phase _ _ _ n); auto.
    assert (locked_by ad t tid <> tid). {
      rewrite locked_by_other with (tid':=tid0); auto.
      apply trace_phase_nonzero with (t:=t); auto; omega.
    }
    rewrite remove_tid_locked_by_neq; auto.
    auto.
  }

  {
    constructor.
    rewrite (remove_tid_phase _ _ _ n); auto.
    intros ad vers I.
    apply in_remove_tid; auto.
    apply H0.
    apply (remove_tid_in tid); auto.
    auto.
  }

  {
    rewrite <- (remove_tid_write_version _ _ _ T P).
    apply complete_write_item_step with (val:=val).
    now rewrite remove_tid_phase.
    assert (locked_by ad t tid <> tid). {
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
    intros ad;
    destruct (Nat.eq_dec (locked_by ad t tid) tid);
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

Lemma write_version_swap t1 t2 ad tid1 tid2 a1 a2:
  action_phase a1 < 4 ->
  write_version ad (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) =
  write_version ad (t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
Proof.
  induction t1; intros AP; cbn in *.

  destruct a1; try solve [ cbn in AP; omega ].
  all: destruct a2; auto.
  all: destruct a; repeat rewrite (IHt1 AP); auto.
Qed.

Lemma locked_by_swap_head t1 t2 ad tid1 tid2 a1 a2 tid:
  locked_by ad ((tid2, a2) :: (tid1, a1) :: t2) tid =
  locked_by ad ((tid1, a1) :: (tid2, a2) :: t2) tid ->
  locked_by ad (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) tid =
  locked_by ad (t1 ++ (tid1, a1) :: (tid2, a2) :: t2) tid.
Proof.
  induction t1; cbn; auto.
  intros; destruct a; destruct a.
  all: try solve [now apply IHt1].
  all: destruct (Nat.eq_dec ad ad0); auto.
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
  | read_item _ _
  | validate_read_item _ _
  | lock_write_item _
  | complete_write_item _ _
  | unlock_write_item _ => False
  | _ => True
  end.

Definition action_commute_read ad a :=
  match a with
  | lock_write_item ad'
  | complete_write_item ad' _
  | unlock_write_item ad' => ad <> ad'
  | _ => True
  end.

Local Ltac check_action :=
  match goal with
  | [ H: action_internal ?a, H2: ?b = ?a |- _ ] =>
    (tryif is_var a then rewrite <- H2 in *; clear H2 else idtac);
    cbn in H; try contradiction; clear H
  | [ H: action_commute_read ?ad ?a, H2: ?b = ?a |- _ ] =>
    (tryif is_var a then rewrite <- H2 in *; clear H2 else idtac);
    cbn in H; try contradiction
  | [ H: action_phase ?a < _, H2: ?b = ?a |- _ ] =>
    (tryif is_var a then rewrite <- H2 in *; clear H2 else idtac);
    cbn in H; try omega
  | [ H: action_phase ?a < _ |- _ ] =>
    cbn in H; try omega
  | [ H: _ <= action_phase ?a, H2: ?b = ?a |- _ ] =>
    (tryif is_var a then rewrite <- H2 in *; clear H2 else idtac);
    cbn in H; try omega
  | [ H: _ <= action_phase ?a |- _ ] =>
    cbn in H; try omega
  end.
Local Ltac fix_phase :=
  match goal with
  | [ TP: tid_phase ?tid ?x = tid_phase ?tid _
      |- context [ tid_phase ?tid ?x ] ] => now rewrite TP
  | [ TP: tid_phase ?tid _ = tid_phase ?tid ?x
      |- context [ tid_phase ?tid ?x ] ] => now rewrite <- TP
  | [ L: context [ locked_by ?ad ?t ?a = ?x ]
      |- locked_by ?ad (_ :: ?t) ?a = ?x ] => cbn; apply L
  | [ L: context [ locked_by ?ad ?t ?a <> ?x ]
      |- locked_by ?ad (_ :: ?t) ?a <> ?x ] => cbn; apply L
  | [ L: context [ locked_by ?ad (?c ?ad1 :: ?t) ?a = ?x ],
      N: ?ad <> ?ad1 |- locked_by ?ad ?t ?a = ?x ] =>
    cbn in L; 
    let X := fresh in
    destruct (Nat.eq_dec ad ad1) as [X|X];
    [ congruence | ]; clear X; apply L
  | [ L: context [ locked_by ?ad (_ :: ?t) ?a = ?x ]
      |- locked_by ?ad ?t ?a = ?x ] => cbn in L; apply L
  | [ L : forall _, locked_by _ ?t ?a = ?x
      |- forall _, locked_by _ ?t ?a = ?x ] =>
      let ad := fresh in intros ad; cbn; apply L
  | [ L : forall _, locked_by _ ?t ?a <> ?x
      |- forall _, locked_by _ ?t ?a <> ?x ] =>
      let ad := fresh in intros ad; cbn; apply L
  | [ L : forall _, locked_by _ ?t ?a = ?x
      |- forall _, locked_by _ (_ :: ?t) ?a = ?x ] =>
      let ad := fresh in intros ad; cbn; apply L
  | [ L : forall _, locked_by _ ?t ?a <> ?x
      |- forall _, locked_by _ (_ :: ?t) ?a <> ?x ] =>
      let ad := fresh in intros ad; cbn; apply L
  | [ |- context [ locked_by ?ad ?t ?a ] ] =>
      intros ad; fix_phase
  | [ WV: write_version ?ad ?t = ?x
      |- write_version ?ad (_ :: ?t) = ?x ] => cbn; apply WV
  | [ LW: tid_last_write ?tid ?ad ?t = ?x
      |- tid_last_write ?tid ?ad ((?tid2, ?a) :: ?t) = ?x ] =>
    cbn; destruct (Nat.eq_dec tid tid2); [ congruence | apply LW ]
  | [ LW: tid_last_write ?tid ?ad ((?tid2, ?a) :: ?t) = ?x
      |- tid_last_write ?tid ?ad ?t = ?x ] =>
    cbn in LW; destruct (Nat.eq_dec tid tid2); [ congruence | apply LW ]
  | [ H: In ?p ?t
      |- In ?p (_ :: ?t) ] => right; apply H
  | [ H: In ?p (_ :: ?t)
      |- In ?p ?t ] => destruct H; [ congruence | apply H ]
  | [ |- context [ In (?tid, _) _ ] ] =>
    let ad := fresh in
    let vx := fresh in
    let I := fresh in
    intros ad vx I; destruct I; [ congruence | right; revert ad vx I; assumption ]
  | [ H: ~ In ?p ?t
      |- ~ In ?p (?x :: ?t) ] => contradict H; destruct H; [ congruence | assumption ]
  | [ H: ~ In ?p (?x :: ?t)
      |- ~ In ?p ?t ] => contradict H; right; assumption
  | [ |- sto_trace ((?tid, start_txn) :: ?t) ] =>
    constructor; [ fix_phase | assumption | auto ]
  | [ |- sto_trace ((?tid, read_item _ _) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, write_item _ _) :: ?t) ] =>
    constructor; [ fix_phase | assumption ]
  | [ |- sto_trace ((?tid, try_commit_txn) :: ?t) ] =>
    constructor; [ fix_phase | assumption ]
  | [ H: In (?tid, write_item ?ad ?vv) _
      |- sto_trace ((?tid, lock_write_item ?ad) :: ?t) ] =>
    apply lock_write_item_step with (v:=vv); [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, seq_point) :: ?t) ] =>
    constructor; [ fix_phase | | assumption ]
  | [ |- sto_trace ((?tid, validate_read_item _ _) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, abort_txn) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, unlock_write_item _) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, commit_txn) :: ?t) ] =>
    constructor; [ fix_phase .. | | assumption ]
  | [ LW: tid_last_write ?tid ?ad _ = Some ?vx
      |- sto_trace ((?tid, complete_write_item ?ad (S (write_version ?ad ?t))) :: ?t) ] =>
    apply complete_write_item_step with (val:=vx);
    [ fix_phase .. | assumption ]
  | [ |- sto_trace ((?tid, commit_done_txn) :: ?t) ] =>
    constructor; [ fix_phase .. | assumption ]
  | [ |- write_version ?ad ?t = write_version ?ad (?p :: ?t) ] =>
    cbn; reflexivity
  | [ H: In ?p (?a :: ?t) |- In ?p ?t ] =>
    destruct H; [ congruence | assumption ]
  | [ H: ~ In ?p (?a :: ?t) |- ~ In ?p ?t ] =>
    contradict H; now right
  | _ => idtac
  end.
Local Ltac chomp1 :=
  match goal with
  | [ |- sto_trace ((?tid, start_txn) :: _ :: _) ] =>
    constructor; [ | assumption | ]; fix_phase
  | [ |- sto_trace ((?tid, read_item ?ad (write_version ?ad ?t)) :: ?p :: ?t) ] =>
    replace (write_version ad t) with (write_version ad (p :: t)) by (now cbn);
    constructor; fix_phase
  | [ |- sto_trace ((?tid, write_item _ _) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, try_commit_txn) :: _ :: _) ] =>
    constructor; fix_phase
  | [ H: In (?tid, write_item ?ad ?vv) _
      |- sto_trace ((?tid, lock_write_item ?ad) :: _ :: _) ] =>
    apply lock_write_item_step with (v:=vv); fix_phase
  | [ |- sto_trace ((?tid, seq_point) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, validate_read_item ?ad ?vers) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, abort_txn) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, unlock_write_item ?ad) :: _ :: _) ] =>
    constructor; fix_phase
  | [ |- sto_trace ((?tid, commit_txn) :: _ :: _) ] =>
    constructor; fix_phase
  | [ H: tid_last_write ?tid ?ad _ = Some ?vx
      |- sto_trace ((?tid, complete_write_item ?ad (S (write_version ?ad ?t))) :: ?p :: ?t) ] =>
    replace (write_version ad t) with (write_version ad (p :: t)) by (now cbn);
    apply complete_write_item_step with (val:=vx); fix_phase
  | [ |- sto_trace ((?tid, commit_done_txn) :: _ :: _) ] =>
    constructor; fix_phase
  end.

Ltac cln :=
  match goal with
  | [ |- context [ Nat.eq_dec ?a ?a ] ] =>
    let X := fresh in
    destruct (Nat.eq_dec a a) as [X|X]; [ | congruence ]; clear X
  | [ H : context [ Nat.eq_dec ?a ?a ] |- _ ] =>
    let X := fresh in
    destruct (Nat.eq_dec a a) as [X|X]; [ | congruence ]; clear X
  | [ H : ?a = ?b |- context [ Nat.eq_dec ?a ?b ] ] =>
    let X := fresh in
    destruct (Nat.eq_dec a b) as [X|X]; [ | congruence ]; clear X
  | [ H : ?a = ?b, P : context [ Nat.eq_dec ?a ?b ] |- _ ] =>
    let X := fresh in
    destruct (Nat.eq_dec a b) as [X|X]; [ | congruence ]; clear X
  | [ H : ?a <> ?b |- context [ Nat.eq_dec ?a ?b ] ] =>
    let X := fresh in
    destruct (Nat.eq_dec a b) as [X|X]; [ congruence | ]; clear X
  | [ H : ?a <> ?b, P : context [ Nat.eq_dec ?a ?b ] |- _ ] =>
    let X := fresh in
    destruct (Nat.eq_dec a b) as [X|X]; [ congruence | ]; clear X
  | [ H : ?a = ?b |- context [ Nat.eq_dec ?b ?a ] ] =>
    let X := fresh in
    destruct (Nat.eq_dec b a) as [X|X]; [ | congruence ]; clear X
  | [ H : ?a = ?b, P : context [ Nat.eq_dec ?b ?a ] |- _ ] =>
    let X := fresh in
    destruct (Nat.eq_dec b a) as [X|X]; [ | congruence ]; clear X
  | [ H : ?a <> ?b |- context [ Nat.eq_dec ?b ?a ] ] =>
    let X := fresh in
    destruct (Nat.eq_dec b a) as [X|X]; [ congruence | ]; clear X
  | [ H : ?a <> ?b, P : context [ Nat.eq_dec ?b ?a ] |- _ ] =>
    let X := fresh in
    destruct (Nat.eq_dec b a) as [X|X]; [ congruence | ]; clear X
  | [ H : ?a <= ?b |- context [ ?a <=? ?b ] ] =>
    rewrite (leb_correct _ _ H)
  | [ H : S ?a <= ?b |- context [ ?a <=? ?b ] ] =>
    rewrite (leb_correct _ _ (le_Sn_le _ _ H))
  | [ H : ?a < ?b |- context [ ?a <? ?b ] ] =>
    let X := fresh in
    assert (a <? b = true) as X by (rewrite Nat.ltb_lt; apply H);
    rewrite X; clear X
  | [ |- context [ _ || true ] ] =>
    rewrite orb_true_r
  | [ |- context [ true || _ ] ] =>
    rewrite orb_true_l
  end.


Lemma swap_internal_back tid1 tid2 a1 a2 t:
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
    all: intros ad' vx I.
    all: assert (In (tid2, write_item ad' vx) t0) as II by (rewrite H1; now right).
    all: rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - inversion T1; chomp1.
  - inversion T1; chomp1.
    all: intros ad' vers' I.
    all: assert (In (tid2, read_item ad' vers') t0) as II by (rewrite H1; now right).
    all: rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - assert (tid2 > 0) by (apply (trace_in_nonzero _ commit_done_txn _ T); now left).
    inversion T1; chomp1.
    all: rewrite <- H6 in *; cbn in H3; try assumption.
    all: intros ad0; destruct (Nat.eq_dec ad ad0).
    1,3,5: rewrite <- e.
    rewrite H10; auto.
    1,2: rewrite H9; auto.
    all: generalize (H3 ad0).
    all: destruct (Nat.eq_dec ad0 ad); try congruence.
Qed.

Lemma swap_internal_forward tid1 tid2 a1 a2 t:
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
    replace (write_version ad ((tid1, a1) :: t)) with (write_version ad t) in *.
    inversion T1; check_action; chomp1.
    destruct a1; cbn in Int; try contradiction Int; cbn; reflexivity.
  - inversion T1; chomp1.
  - inversion T1; chomp1.
  - inversion T1; check_action; chomp1.
    intros adx; cbn; destruct (Nat.eq_dec adx ad); congruence.
  - inversion T1; chomp1.
    all: intros adx vx I.
    all: assert (In (tid2, write_item adx vx) t0) as II by (rewrite H1; now right).
    all: rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - inversion T1; check_action; subst; chomp1.
  - inversion T1; chomp1.
  - inversion T1; check_action; chomp1.
    assert (tid1 > 0) as TZ by (apply (trace_in_nonzero _ commit_done_txn _ T1); now left).
    intros adx; cbn; destruct (Nat.eq_dec adx ad); auto.
  - inversion T1; chomp1.
    all: intros adx vers' I.
    all: assert (In (tid2, read_item adx vers') t0) as II by (rewrite H1; now right).
    all: rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - rewrite H1 in *; clear H1.
    replace (write_version ad ((tid1, a1) :: t)) with (write_version ad t) in *.
    inversion T1; check_action; chomp1.
    assert (tid1 > 0) as TZ by (apply (trace_in_nonzero _ commit_done_txn _ T1); now left).
    intros adx; cbn; destruct (Nat.eq_dec adx ad); auto; omega.
    destruct a1; cbn in Int; try contradiction Int; cbn; reflexivity.
  - assert (tid2 > 0) as TZ by (apply (trace_in_nonzero _ commit_done_txn _ T); now left).
    inversion T1; chomp1.
    all: intros adx.
    all: rewrite <- H5 in *; clear H5.
    all: cbn in H3; try apply H3.
    all: generalize (H3 adx); intros XX.
    all: destruct (Nat.eq_dec adx ad); auto.
Qed.

Lemma swap_read_back tid1 tid2 ad v a1 t:
  sto_trace ((tid2, read_item ad v) :: (tid1, a1) :: t) ->
  action_commute_read ad a1 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, a1) :: (tid2, read_item ad v) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, read_item ad v) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T.
  assert (write_version ad ((tid1, a1) :: t) = write_version ad t) as WV. {
    destruct a1; cbn; auto.
    destruct (Nat.eq_dec ad ad1); auto.
    rewrite <- e in Int; cbn in Int; contradiction.
  }
  rewrite WV.
  rename H5 into T1.

  inversion T1; check_action; chomp1.
  all: cbn; destruct (Nat.eq_dec tid1 tid2); [ congruence | auto ].
  all: cbn in H4; destruct (Nat.eq_dec ad ad1) as [X|X]; [congruence|auto].
Qed.

Lemma swap_validate_read_back tid1 tid2 ad v a1 t:
  sto_trace ((tid2, validate_read_item ad v) :: (tid1, a1) :: t) ->
  action_commute_read ad a1 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, a1) :: (tid2, validate_read_item ad v) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, validate_read_item ad v) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, a1) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T.
  assert (write_version ad ((tid1, a1) :: t) = write_version ad t) as WV. {
    destruct a1; cbn; auto.
    destruct (Nat.eq_dec ad ad1); auto.
    cbn in Int; congruence.
  }
  rename H8 into T1.

  inversion T1; check_action; chomp1.
  all: cbn in WV; auto.
  all: cbn in H4, H5; destruct (Nat.eq_dec ad ad1) as [X|X]; [congruence|auto].
Qed.

Lemma swap_read_forward tid1 tid2 ad v a2 t:
  sto_trace ((tid2, a2) :: (tid1, read_item ad v) :: t) ->
  action_commute_read ad a2 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, read_item ad v) :: (tid2, a2) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, read_item ad v) :: t) = tid_phase tid2 t) as TP2. {
    cbn; destruct (Nat.eq_dec tid2 tid1); congruence.
  }

  inversion T; check_action.
  all: match goal with
       | [ H: sto_trace ((?t1, ?a1) :: ?t), H2: sto_trace (?a :: ?b :: ?c) |- _ ] =>
         rename H into T1
       end.
  all: inversion T1.
  - chomp1.
  - chomp1; cbn; auto. now cln. constructor; fix_phase; auto.
  - chomp1.
  - chomp1.
  - chomp1.
    cbn; destruct (Nat.eq_dec ad ad0); [congruence|auto].
  - chomp1.
    intros adx vx I.
    assert (In (tid2, write_item adx vx) t0) as II by (rewrite H1; now right).
    rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - chomp1. cbn in H4; auto.
  - chomp1.
  - chomp1.
    cbn; destruct (Nat.eq_dec ad ad0); [congruence|auto].
  - chomp1.
    intros adx vers I.
    assert (In (tid2, read_item adx vers) t0) as II by (rewrite H1; now right).
    rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - cbn.
    replace (write_version ad t) with (write_version ad ((tid2, complete_write_item ad0 (S (write_version ad0 t))) :: t)).
    constructor; fix_phase.
    all: cbn; now cln.
  - chomp1.
    intros adx; generalize (H3 adx); intros LL; now cbn in LL.
Qed.

Lemma swap_validate_read_forward tid1 tid2 ad v a2 t:
  sto_trace ((tid2, a2) :: (tid1, validate_read_item ad v) :: t) ->
  action_commute_read ad a2 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, validate_read_item ad v) :: (tid2, a2) :: t).
Proof.
  intros T Int N.
  assert (tid_phase tid1 ((tid2, a2) :: t) = tid_phase tid1 t) as TP1. {
    cbn; destruct (Nat.eq_dec tid1 tid2); congruence.
  }
  assert (tid_phase tid2 ((tid1, validate_read_item ad v) :: t) = tid_phase tid2 t) as TP2. {
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
  - cbn; now cln.
  - intros adx vx I.
    assert (In (tid2, write_item adx vx) t0) as II by (rewrite H1; now right).
    rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - rewrite <- H4; cbn; reflexivity.
  - cbn; now cln.
  - intros adx vers' I.
    assert (In (tid2, read_item adx vers') t0) as II by (rewrite H1; now right).
    rewrite H1 in II; apply H3 in II; destruct II; [ congruence | assumption ].
  - cbn; now cln.
  - cbn; now cln.
  - cbn; now cln.
  - cbn; apply complete_write_item_step with (val:=val);
      fix_phase.
    apply (trace_cons _ _ T1).
  - intros adx; generalize (H3 adx); intros LL.
    now cbn in LL.
Qed.

Definition addresses a ad :=
  match a with
  | read_item ad' _
  | write_item ad' _
  | lock_write_item ad'
  | validate_read_item ad' _
  | unlock_write_item ad'
  | complete_write_item ad' _ => ad = ad'
  | _ => False
  end.

Definition addressof a :=
  match a with
  | read_item ad _
  | write_item ad _
  | lock_write_item ad
  | validate_read_item ad _
  | unlock_write_item ad
  | complete_write_item ad _ => Some ad
  | _ => None
  end.

Definition locked_by_of a t default :=
  match addressof a with
  | Some ad => locked_by ad t default
  | None => default
  end.

Definition write_version_of a t :=
  match addressof a with
  | Some ad => write_version ad t
  | None => 0
  end.

Lemma swap_forward_to_seq_point tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  tid1 <> tid2 ->
  action_phase a1 < 3 ->
  locked_by_of a1 ((tid2, a2) :: t) tid1 = tid1 ->
  write_version_of a1 ((tid2, a2) :: t) = write_version_of a1 t ->
  sto_trace ((tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros T N AP LB WV.
  assert (forall ad, write_version ad ((tid1, a1) :: t) = write_version ad t) as WV1. {
    intros ad; destruct a1; cbn in AP; try omega.
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
  all: try solve [ apply swap_internal_back; [ assumption | now cbn | assumption ] ].
  - rewrite WV1.
    apply swap_read_back; auto.
    rewrite <- WV1; auto.
    destruct a1; cbn in AP; try omega; cbn; auto.
    cbn in H3; destruct (Nat.eq_dec ad ad0); auto; omega.
  - inversion T1; check_action; chomp1.
    cbn; cbn in LB; destruct (Nat.eq_dec ad0 ad); [congruence|auto].
    cbn; cbn in LB; destruct (Nat.eq_dec ad0 ad); [congruence|auto].
    cbn; cbn in H4; destruct (Nat.eq_dec ad ad0); [congruence|auto].
  - apply swap_validate_read_back; auto.
    destruct a1; cbn in AP; try omega; cbn; auto.
    cbn in H3; destruct (Nat.eq_dec ad ad0); [congruence|auto].
  - inversion T1; check_action; chomp1.
    all: cbn; auto.
    1-2: destruct (Nat.eq_dec ad0 ad); auto.
    cbn in H3; destruct (Nat.eq_dec ad ad0); congruence.
  - cbn; inversion T1; check_action; chomp1.
    all: cbn; try now cln.
    1-2: destruct (Nat.eq_dec ad0 ad); auto.
    cbn in H3; destruct (Nat.eq_dec ad ad0); [congruence|auto].
Qed.    

Definition tid_outstanding_read tid ad (t:trace) :=
  exists v, In (tid, read_item ad v) t /\
            ~ In (tid, validate_read_item ad v) t.

Lemma read_outstanding_read tid ad v t:
  sto_trace ((tid, read_item ad v) :: t) ->
  tid_outstanding_read tid ad ((tid, read_item ad v) :: t).
Proof.
  intros T; inversion T.
  exists (write_version ad t); split.
  now left.
  intros F; subst.
  assert (3 <= tid_phase tid ((tid, read_item ad (write_version ad t)) :: t)). {
    replace 3 with (action_phase (validate_read_item ad (write_version ad t))) by (now cbn).
    apply phase_increase_in; auto.
  }
  cbn in H; destruct (Nat.eq_dec tid tid); [ omega | congruence ].
Qed.

Lemma validate_outstanding_read tid ad v t:
  sto_trace ((tid, validate_read_item ad v) :: t) ->
  tid_outstanding_read tid ad t.
Proof.
  intros T; inversion T.
  exists v; split; auto.
Qed.

Lemma permutation_outstanding_read {tid ad t1 t2}:
  Permutation t1 t2 ->
  tid_outstanding_read tid ad t1 ->
  tid_outstanding_read tid ad t2.
Proof.
  intros PE H; unfold tid_outstanding_read in *.
  destruct H as [v [I N]].
  exists v; split.
  now apply (Permutation_in _ PE).
  intros X; apply (Permutation_in _ (Permutation_sym PE)) in X; contradiction.
Qed.


Inductive unconflicted : trace -> Prop :=
| nil_unc: unconflicted []
| internal_unc: forall tid a t,
    unconflicted t ->
    action_internal a ->
    unconflicted ((tid, a) :: t)
| read_unc: forall tid ad v t,
    unconflicted t ->
    locked_by ad t 0 = 0 ->
    write_version ad t = v ->
    unconflicted ((tid, read_item ad v) :: t)
| validate_read_unc: forall tid ad v t,
    unconflicted t ->
    unconflicted ((tid, validate_read_item ad v) :: t)
| lock_unc: forall tid ad t,
    unconflicted t ->
    (forall tid', tid = tid' \/ ~ tid_outstanding_read tid' ad t) ->
    unconflicted ((tid, lock_write_item ad) :: t)
| complete_unc: forall tid ad v t,
    unconflicted t ->
    unconflicted ((tid, complete_write_item ad v) :: t)
| unlock_unc: forall tid ad t,
    unconflicted t ->
    unconflicted ((tid, unlock_write_item ad) :: t).

Lemma unconflicted_cons ta t:
  unconflicted (ta :: t) ->
  unconflicted t.
Proof.
  intros H; inversion H; auto.
Qed.


Definition no_aborted (t:trace) :=
  forall tid a,
    In (tid, a) t ->
    action_phase a <= 4.  

Lemma no_aborted_cons ta t:
  no_aborted (ta :: t) ->
  no_aborted t.
Proof.
  intros NA tid a I.
  apply (NA tid a); now right.
Qed.

Lemma permutation_no_aborted {t1 t2}:
  Permutation t1 t2 ->
  no_aborted t1 ->
  no_aborted t2.
Proof.
  intros PE NA tid a I.
  apply (Permutation_in _ (Permutation_sym PE)) in I.
  apply (NA tid a I).
Qed.


Lemma committed_read_validated tid t ad v:
  sto_trace t ->
  tid_phase tid t = 4 ->
  In (tid, read_item ad v) t ->
  In (tid, validate_read_item ad v) t.
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

Lemma trace_after_lock tid t1 t2 ad:
  sto_trace (t1 ++ (tid, lock_write_item ad) :: t2) ->
  In (tid, unlock_write_item ad) t1
  \/ locked_by ad (t1 ++ (tid, lock_write_item ad) :: t2) 0 = tid
  \/ write_version ad t2 < write_version ad (t1 ++ (tid, lock_write_item ad) :: t2).
Proof.
  induction t1; intros T.
  right; left; cbn; now cln.
  destruct a; inversion T; rewrite <- H0 in *; clear H0.
  all: match goal with
       | [ H: sto_trace (_ ++ _ :: _) |- _ ] =>
         rename H into T1; generalize (IHt1 T1); intros X
       end.
  all: destruct X as [X|[X|X]]; intuition.
  - right; left; cbn.
    destruct (Nat.eq_dec ad ad0); auto.
    rewrite <- e in *; clear e; rewrite H4 in H0.
    enough (tid > 0); [omega|].
    apply (trace_in_nonzero _ (lock_write_item ad) _ T1).
    apply in_or_app; right; now left.
  - destruct (Nat.eq_dec ad ad0).
    rewrite <- e in *; clear e; left; left.
    rewrite <- H0; now rewrite H3.
    right; left; cbn; now cln.
  - cbn; destruct (Nat.eq_dec ad ad0); [rewrite <- e in *; clear e|].
    right; right.
    apply le_lt_n_Sm.
    replace ((tid, lock_write_item ad) :: t2)
    with ([(tid, lock_write_item ad)] ++ t2) by (now cbn).
    rewrite app_assoc.
    apply write_version_increase_app.
    rewrite <- app_assoc; cbn.
    rewrite <- app_comm_cons in *.
    now apply trace_cons in T.
    right; now left.
  - cbn; destruct (Nat.eq_dec ad ad0);
      [right; right; rewrite <- e; auto | right; now left].
  - cbn; destruct (Nat.eq_dec ad ad0);
      [right; right; rewrite <- e; auto | right; now left].
  - cbn; destruct (Nat.eq_dec ad ad0);
      [right; right; rewrite <- e; auto | right; now right].
Qed.
  
Lemma nonaborted_read_validate_different tid tid' t1 t2 ad v:
  sto_trace (t1 ++ (tid, lock_write_item ad) :: t2) ->
  tid_phase tid (t1 ++ (tid, lock_write_item ad) :: t2) < 6 ->
  tid <> tid' ->
  In (tid', read_item ad v) t2 ->
  ~ In (tid', validate_read_item ad v) t1.
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
  rename H7 into T1.
  generalize (trace_after_lock _ _ _ _ T1); intros X.
  destruct X as [X | [X | X]].
  - assert (6 <= tid_phase tid (t1 ++ (tid, lock_write_item ad) :: t2)). {
      replace 6 with (action_phase (unlock_write_item ad)) by (now cbn).
      apply phase_increase_in; auto.
      apply in_or_app; now left.
    }
    omega.
  - apply (locked_by_other tid0) in X; auto.
    congruence.
    apply (trace_in_nonzero _ (lock_write_item ad) _ T1).
    apply in_or_app; right; now left.
  - inversion F; rewrite <- H7, H8 in *; clear H7 H8 F.
    rewrite H4 in *; clear vers H4.
    assert (v <= write_version ad0 t2). {
      apply read_version_increase_in with (tid0:=tid').
      apply trace_app in T1; now apply trace_cons in T1.
      auto.
    }
    omega.
Qed.

Lemma committable_unconflicted t:
  sto_trace t ->
  (exists t2, sto_trace (t2 ++ t) /\ all_committed (t2 ++ t)) ->
  unconflicted t.
Proof.
  intros T; induction T; intros NU; destruct NU as [t2 [NU1 NU2]].
  1: constructor.
  Local Ltac myexists :=
    match goal with
    | [ IHT: ?a -> unconflicted ?t1,
        H: sto_trace (?t2 ++ ?p :: ?t1) |- _ ] =>
      apply IHT; exists (t2 ++ [p]); rewrite <- app_assoc; cbn; split; auto
    end.
  all: try solve [apply internal_unc; [| cbn]; auto; myexists].
  - apply read_unc; auto; myexists.
  - apply lock_unc; [ myexists | ].
    remember (t2 ++ (tid0, lock_write_item ad) :: t) as tb.
    intros tid; destruct (Nat.eq_dec tid0 tid); [ now left | right ].
    intros F; destruct F as [vers [ER ENV]].
    assert (tid_phase tid tb = 4) as TP4X. {
      apply NU2.
      assert (In (tid, read_item ad vers) tb) as EX. {
        rewrite Heqtb; apply in_or_app; right; now right.
      }
      apply phase_increase_in in EX; cbn in EX; auto; omega.
    }
    assert (In (tid, read_item ad vers) tb) as ERX. {
      rewrite Heqtb; apply in_or_app; right; now right.
    }
    generalize (committed_read_validated _ _ _ _ NU1 TP4X ERX); intros EVXB.
    assert (In (tid, validate_read_item ad vers) t2) as EVX. {
      rewrite Heqtb in EVXB; apply in_app_or in EVXB.
      destruct or EVXB; auto.
      destruct EVXB; [ congruence | contradiction ].
    }
    clear TP4X ENV EVXB.
    rewrite Heqtb in NU1;
      apply nonaborted_read_validate_different with (tid':=tid) (v:=vers) in NU1.
    contradiction.
    assert (tid_phase tid0 tb = 4) as TP4. {
      apply NU2.
      assert (In (tid0, lock_write_item ad) tb) as EX. {
        rewrite Heqtb; apply in_or_app; right; now left.
      }
      apply phase_increase_in in EX; cbn in EX.
      omega.
      now rewrite Heqtb.
    }
    unfold Top.tid in *; rewrite <- Heqtb; omega.
    auto.
    auto.
  - apply validate_read_unc; auto; myexists.
  - apply unlock_unc; auto; myexists.
  - apply complete_unc; auto; myexists.
Qed.

Lemma swap_forward_unconflicted tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
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
      by (now apply (trace_cons _ _ T)).
  destruct a1; cbn in AP; try omega.
  all: inversion T1.

  1, 3, 4: apply swap_internal_forward; cbn; auto.

  - replace (write_version ad t) with (write_version ad ((tid2, a2) :: t)).
    constructor.
    now rewrite TP1.
    {
      destruct a2; cbn; auto.
      inversion U.
      check_action.
      destruct (Nat.eq_dec ad ad1); [rewrite <- e in *; clear e|]; auto.
      generalize (H10 tid1); intros X; destruct X as [X | X].
      congruence.
      contradict X.
      apply read_outstanding_read; auto.

      destruct (Nat.eq_dec ad ad1); auto.
      destruct (Nat.eq_dec ad ad1); auto.
    }
    {
      destruct a2; inversion T.
      all: try constructor; fix_phase; auto.
      cbn; constructor; fix_phase; auto.
      intros adx vv I.
      assert (In (tid2, write_item adx vv) ((tid1, read_item ad vers) :: t)) as II by (now right).
      apply (H9 adx vv) in II; destruct II; [ congruence | assumption ].
      intros adx vers' I.
      assert (In (tid2, read_item adx vers') ((tid1, read_item ad vers) :: t)) as II by (now right).
      apply (H9 adx vers') in II; destruct II; [ congruence | assumption ].
      rewrite H9 in *; clear H9.
      cbn in *.
      apply complete_write_item_step with (val:=val); fix_phase; auto.
      destruct (Nat.eq_dec tid2 tid1); [ congruence | assumption ].
      destruct (Nat.eq_dec tid2 tid1); assumption.
    }
    {
      destruct a2; cbn; auto.
      inversion T.
      destruct (Nat.eq_dec ad ad1); auto.
      rewrite <- e in *; clear e.
      inversion H13.
      cbn in H11; rewrite H11 in H19; omega.
    }

  - apply lock_write_item_step with (v:=v).
    now rewrite TP1.
    now right.
    cbn; destruct a2; auto.
    destruct (Nat.eq_dec ad ad1); auto.
    rewrite <- e in *; clear e.
    inversion T; simpl in H11; cln.
    omega.
    destruct (Nat.eq_dec ad ad1); auto.
    destruct (Nat.eq_dec ad ad1); auto.
    destruct a2; inversion T.
    all: try solve [ cbn in *; contradiction ].
    all: try constructor; fix_phase; auto.
    cbn; constructor; cbn in H9; cln; auto.
    cbn in H11; destruct (Nat.eq_dec ad1 ad); [omega|auto].
    cbn in H11; destruct (Nat.eq_dec ad1 ad); [omega|auto].
    intros adx vv I.
    assert (In (tid2, write_item adx vv) ((tid1, lock_write_item ad) :: t)) as II by (now right).
    apply (H9 adx vv) in II; destruct II; [ congruence | assumption ].
    cbn in H11; destruct (Nat.eq_dec ad1 ad); [congruence|auto].
    cbn in H10; destruct (Nat.eq_dec ad1 ad); [congruence|auto].
    intros adx vers I.
    assert (In (tid2, read_item adx vers) ((tid1, lock_write_item ad) :: t)) as II by (now right).
    apply (H9 adx vers) in II; destruct II; [ congruence | assumption ].
    cbn; apply complete_write_item_step with (val:=val); auto.
    fix_phase.
    cbn in H11; destruct (Nat.eq_dec ad1 ad); [congruence|auto].
    cbn in H12; destruct (Nat.eq_dec tid2 tid1); auto.
    intros adx.
    enough (locked_by adx ((tid1, lock_write_item ad) :: t) 0 <> tid2).
    cbn in H12; destruct (Nat.eq_dec adx ad); auto.
    rewrite e; rewrite H4; omega.
    apply H9.
Qed.

Lemma swap_backward_committing tid1 tid2 a1 a2 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
  3 <= action_phase a2 ->
  action_phase a2 <= 4 ->
  action_phase a1 <> 6 ->
  tid1 <> tid2 ->
  sto_trace ((tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros T U AP2 AP2B AP1 N.
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
      by (now apply (trace_cons _ _ T)).
  inversion T1; rewrite <- H0 in *; clear H0.
  all: cbn in AP1; try congruence; clear AP1.
  all: try repeat rewrite H, H1 in *; clear H.

  all: try solve [apply swap_internal_forward; cbn; auto].
  rewrite H1 in *; clear H1; apply swap_forward_unconflicted; auto.

  all: destruct a2; cbn in AP2; cbn in AP2B; try omega.
  all: clear AP2 AP2B.
  all: try solve [apply swap_internal_back; cbn; auto].
  all: inversion T; try rewrite H1 in *; clear H1.

  Local Ltac chomp2 :=
    match goal with
    | [ L1: locked_by ((?t1, _) :: ?t) _ = _,
        L2: locked_by ?t _ = _ |- _ ] =>
      cbn in L1; congruence || chomp2 || idtac
    | [ L1: locked_by ?t ?v = ?v,
        L2: locked_by ?t 0 = ?x |- _ ] =>
      apply locked_by_self_or in L1; destruct or L1; congruence || omega || idtac
    end.

  - apply lock_write_item_step with (v:=v); fix_phase.
    cbn in H9; destruct (Nat.eq_dec ad0 ad); [congruence|auto].
    now cbn in H10.
  - apply lock_write_item_step with (v:=v); cbn; fix_phase.
    destruct (Nat.eq_dec tid1 tid2); [congruence|auto].
    now right.
    destruct (Nat.eq_dec ad ad0); auto.
    cbn in H9; destruct (Nat.eq_dec ad0 ad); [congruence|auto].
  - constructor; cbn in *; fix_phase; auto.
    destruct (Nat.eq_dec tid1 tid2); destruct (Nat.eq_dec tid2 tid1); try congruence; auto.
    inversion T1.
    contradict H14.
    destruct H14; [now left|contradiction].
    destruct (Nat.eq_dec tid2 tid1); [congruence|auto].
    destruct H13; [congruence|auto].
  - cbn in *; constructor; fix_phase; cln; auto.
    cbn; destruct (Nat.eq_dec tid1 tid2); [congruence|auto].
    destruct (Nat.eq_dec tid2 tid1); [omega|].
    cbn; destruct (Nat.eq_dec ad ad0); auto.
    cbn; destruct (Nat.eq_dec ad ad0); auto.
    rewrite <- e in *; clear e.
    apply locked_by_self_or in H3; destruct H3; rewrite H1 in *; [omega|congruence].
    apply complete_write_item_step with (val:=val); auto.
    cln; auto.
    now destruct (Nat.eq_dec tid2 tid1).
  - replace (write_version ad t) with (write_version ad ((tid2, seq_point) :: t)).
    apply complete_write_item_step with (val:=val); cbn; fix_phase; auto.
    now cln.
    now cln.
    intros adx vx I.
    enough (In (tid2, lock_write_item adx) ((tid1, complete_write_item ad (S (write_version ad t))) :: t)).
    destruct H1; [congruence|auto].
    apply (H7 adx vx); now right.
    now cbn.
  - assert (ad0 <> ad) as AD. {
      destruct (Nat.eq_dec ad0 ad); [|auto].
      rewrite e in *; clear e.
      cbn in H10; cln; rewrite H10 in *.
      cbn in H11; destruct H11; [congruence|].
      apply read_version_increase_in in H1.
      rewrite <- H10 in H1; omega.
      apply (trace_cons _ _ H13).
    }
    replace (write_version ad t) with (write_version ad ((tid2, validate_read_item ad0 vers) :: t)).
    apply complete_write_item_step with (val:=val); cbn; fix_phase; auto.
    now cln.
    now cln.
    cbn in H9; destruct (Nat.eq_dec ad0 ad); [congruence|auto].
    cbn in H10; destruct (Nat.eq_dec ad0 ad); [congruence|auto].
    now cbn.
  - apply swap_internal_back; cbn; auto.
  - assert (ad0 <> ad) as AD. {
      destruct (Nat.eq_dec ad0 ad); [|auto].
      rewrite e, H7 in *; clear e H7.
      cbn in H9; cln; omega.
    }
    cbn; cln.
    replace (write_version ad t) with (write_version ad ((tid2, complete_write_item ad0 (S (write_version ad0 t))) :: t)).
    apply complete_write_item_step with (val:=val); cbn; fix_phase; auto.
    now cln.
    now cln.
    now cln.
    cbn in H9; now cln.
    cbn; now cln.
  - apply swap_internal_back; cbn; auto.
Qed.


(** Facts about [tid_phase] and permutations *)

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
  rewrite <- (IHt (trace_cons _ _ T)).
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


(** Facts about serial permutations *)

Definition trace_same_end_state t1 t2 :=
  Permutation t1 t2
  /\ (forall ad, locked_by ad t1 0 = locked_by ad t2 0)
  /\ (forall ad, write_version ad t1 = write_version ad t2)
  /\ (forall tid ad, tid_last_write tid ad t1 = tid_last_write tid ad t2).

Lemma trace_same_end_state_cons t1 t2 a:
  trace_same_end_state t1 t2 ->
  trace_same_end_state (a :: t1) (a :: t2).
Proof.
  intros S; destruct S as [P [L [WV LW]]].
  split; [ | split; [ | split ]].
  - now apply perm_skip.
  - intros ad; destruct a; destruct a; cbn; auto.
    all: destruct (Nat.eq_dec ad ad0); auto.
  - intros ad; destruct a; destruct a; cbn; auto.
    all: destruct (Nat.eq_dec ad ad0); auto.
  - intros tid ad; destruct a; destruct a; cbn; auto.
    all: destruct (Nat.eq_dec tid t); auto.
    all: destruct (Nat.eq_dec ad ad0); auto.
Qed.

Lemma trace_same_end_state_app t1 t2 th:
  trace_same_end_state t1 t2 ->
  trace_same_end_state (th ++ t1) (th ++ t2).
Proof.
  induction th; intros S; cbn; auto.
  apply trace_same_end_state_cons; auto.
Qed.



Lemma sto_trace_permutation_cons t1 t2 tid a:
  sto_trace ((tid, a) :: t1) ->
  sto_trace t2 ->
  trace_same_end_state t1 t2 ->
  sto_trace ((tid, a) :: t2).
Proof.
  intros T1X T2 S.
  unfold trace_same_end_state in S.
  destruct S as [P [L [WV LW]]].
  assert (Permutation t2 t1) as P' by (now apply Permutation_sym).
  assert (sto_trace t1) as T1 by (apply (trace_cons _ _ T1X)).
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
    intros ad vv I.
    apply Permutation_in with (l:=t1); auto.
    apply (H3 ad vv).
    apply Permutation_in with (l:=t2); auto.
  - constructor; try rewrite <- PE; auto.
    apply locked_by_self_or in H3.
    destruct or H3.
    rewrite L in H3; apply locked_by_unlocked; auto.
    rewrite L in H3; apply locked_by_self; auto.
    now rewrite <- WV.
    apply Permutation_in with (l:=t1); auto.
    contradict H6.
    apply Permutation_in with (l':=t1) in H6; auto.
  - constructor; try rewrite <- PE; auto.
  - constructor; try rewrite <- PE; auto.
    now rewrite <- L.
  - constructor; try rewrite <- PE; auto.
    intros ad vv I.
    apply Permutation_in with (l:=t1); auto.
    apply H3.
    apply Permutation_in with (l:=t2); auto.
  - rewrite WV.
    apply complete_write_item_step with (val:=val); try rewrite <- PE; auto.
    now rewrite <- L.
    now rewrite <- LW.
  - constructor; try rewrite <- PE; auto.
    intros ad; now rewrite <- L.
    contradict H4.
    apply Permutation_in with (l:=t2); auto.
Qed.

Lemma sto_trace_permutation_app t1 t2 th:
  sto_trace (th ++ t1) ->
  sto_trace t2 ->
  trace_same_end_state t1 t2 ->
  sto_trace (th ++ t2).
Proof.
  induction th; intros T1X T2 S.
  simpl; auto.
  rewrite <- app_comm_cons in *.
  assert (trace_same_end_state (th ++ t1) (th ++ t2)) by
      (now apply trace_same_end_state_app).
  destruct a.
  apply sto_trace_permutation_cons with (t1 := th ++ t1); auto.
  apply IHth; auto.
  apply (trace_cons _ _ T1X).
Qed.

Lemma unconflicted_permutation_cons t1 t2 tid a:
  unconflicted ((tid, a) :: t1) ->
  unconflicted t2 ->
  trace_same_end_state t1 t2 ->
  unconflicted ((tid, a) :: t2).
Proof.
  intros T1X T2 S.
  unfold trace_same_end_state in S.
  destruct S as [P [L [WV LW]]].
  inversion T1X.
  - apply internal_unc; auto.
  - apply read_unc; congruence.
  - apply validate_read_unc; auto.
  - apply lock_unc; auto.
    intros tid'; generalize (H3 tid'); intros X; destruct X.
    now left.
    right; contradict H4; apply @permutation_outstanding_read with (t1:=t2); auto.
    now apply Permutation_sym.
  - apply complete_unc; auto.
  - apply unlock_unc; auto.
Qed.

Lemma trace_same_end_state_unconflicted_forward tid2 a2 tid1 a1 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
  action_phase a1 < 3 ->
  tid1 <> tid2 ->
  trace_same_end_state ((tid2, a2) :: (tid1, a1) :: t)
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
  - intros adx.
    cbn; destruct a1; check_action; destruct a2; try congruence.
    all: inversion T; cbn in *; try congruence.
    all: destruct (Nat.eq_dec adx ad0); destruct (Nat.eq_dec adx ad); auto.
    all: subst; repeat cln; omega.
  - intros adx.
    cbn; destruct a1; check_action; destruct a2; try congruence.
    all: inversion T; cbn in *; try congruence.
    all: destruct (Nat.eq_dec adx ad0); destruct (Nat.eq_dec ad0 ad); auto.
    all: subst; repeat cln; omega.
  - intros tid adx.
    cbn; destruct a1; check_action; destruct a2; try congruence.
    all: destruct (Nat.eq_dec tid tid1); destruct (Nat.eq_dec tid tid2);
      congruence.
Qed.

Lemma trace_same_end_state_unconflicted_backward tid2 a2 tid1 a1 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
  3 <= action_phase a2 ->
  tid1 <> tid2 ->
  trace_same_end_state ((tid2, a2) :: (tid1, a1) :: t)
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
  - intros adx.
    cbn; destruct a2; check_action; destruct a1; try congruence.
    all: inversion T; cbn in *; try congruence.
    all: destruct (Nat.eq_dec adx ad); destruct (Nat.eq_dec adx ad0); auto.
    all: subst; repeat cln; omega.
  - intros adx.
    cbn; destruct a2; check_action; destruct a1; try congruence.
    all: inversion T; cbn in *; try congruence.
    all: destruct (Nat.eq_dec adx ad); destruct (Nat.eq_dec adx ad0); auto.
    all: subst; repeat cln; omega.
  - intros tid adx.
    cbn; destruct a2; check_action; destruct a1; try congruence.
    all: destruct (Nat.eq_dec tid tid1); destruct (Nat.eq_dec tid tid2);
      congruence.
Qed.

Lemma unconflicted_unconflicted_forward tid2 a2 tid1 a1 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
  action_phase a1 < 3 ->
  tid1 <> tid2 ->
  unconflicted ((tid1, a1) :: (tid2, a2) :: t).
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
  assert (unconflicted ((tid1, a1) :: t)) as U1. {
    apply (unconflicted_cons _ _ U).
  }
  assert (unconflicted t) as UX. {
    apply (unconflicted_cons _ _ U1).
  }
  assert (unconflicted ((tid2, a2) :: t)) as U2. {
    inversion U.
    - now apply internal_unc.
    - apply read_unc; auto.
      + destruct a1; cbn in H3; check_action; auto.
        destruct (Nat.eq_dec ad ad0); [omega|auto].
      + destruct a1; cbn in H4; check_action; auto.
    - apply validate_read_unc; auto.
    - apply lock_unc; auto.
      intros tid'.
      generalize (H3 tid'); intros HX; destruct or HX.
      now left.
      right; contradict HX.
      destruct HX as [V [I NI]].
      exists V; split.
      now right.
      contradict NI.
      destruct NI; auto.
      inversion H4; subst; cbn in AP; omega.
    - apply complete_unc; auto.
    - apply unlock_unc; auto.
  }
  inversion U1.
  - now apply internal_unc.
  - apply read_unc; auto.
    + destruct a2; cbn; auto.
      all: destruct (Nat.eq_dec ad ad0); auto.
      rewrite <- e in *; clear e.
      subst.
      inversion U; [ cbn in *; contradiction | ].
      generalize (H5 tid1); intros X; destruct X.
      congruence.
      contradict H6.
      exists (write_version ad t).
      split; [ now left | ].
      intros I; destruct I as [I|I].
      inversion I.
      apply phase_increase_in in I; simpl in I; auto.
      apply trace_cons in T; apply phase_increase_head in T; omega.
      do 2 apply trace_cons in T; auto.
    + destruct a2; cbn; auto.
      destruct (Nat.eq_dec ad ad0); auto.
      rewrite <- H0 in *; clear a1 H0.
      rewrite <- e in *; clear ad0 e.
      inversion T.
      cbn in H9; rewrite H3 in H9; omega.
  - apply validate_read_unc; auto.
  - apply lock_unc; auto.
    intros t'; generalize (H3 t'); intros X; destruct X.
    now left.
    right; contradict H4.
    destruct H4 as [V [I NI]]; exists V; split.
    destruct I as [I|I]; auto.
    inversion I; subst.
    inversion U; [cbn in *; contradiction|].
    simpl in H6; cln; omega.
    contradict NI; now right.
  - apply complete_unc; auto.
  - apply unlock_unc; auto.
Qed.

Lemma unconflicted_unconflicted_backward tid2 a2 tid1 a1 t:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  unconflicted ((tid2, a2) :: (tid1, a1) :: t) ->
  3 <= action_phase a2 ->
  tid1 <> tid2 ->
  unconflicted ((tid1, a1) :: (tid2, a2) :: t).
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
  assert (unconflicted ((tid1, a1) :: t)) as U1. {
    apply (unconflicted_cons _ _ U).
  }
  assert (unconflicted t) as UX. {
    apply (unconflicted_cons _ _ U1).
  }
  assert (unconflicted ((tid2, a2) :: t)) as U2. {
    inversion U; subst.
    - now apply internal_unc.
    - apply read_unc; auto.
      + destruct a1; check_action; auto.
      + destruct a1; check_action; auto.
    - apply validate_read_unc; auto.
    - apply lock_unc; auto.
      intros tid'.
      generalize (H3 tid'); intros HX; destruct or HX.
      now left.
      right; contradict HX.
      destruct HX as [V [I NI]].
      exists V; split.
      now right.
      contradict NI.
      destruct NI as [NI|NI]; auto.
      inversion NI; subst; cbn in AP; omega.
    - apply complete_unc; auto.
    - apply unlock_unc; auto.
  }
  inversion U1.
  - now apply internal_unc.
  - apply read_unc; auto.
    + destruct a2; check_action; auto.
      all: cbn; destruct (Nat.eq_dec ad ad0); auto.
    + destruct a2; check_action; auto.
      all: cbn; destruct (Nat.eq_dec ad ad0); auto.
      rewrite <- H0 in *; rewrite <- e in *; clear a1 H0 ad0 e.
      inversion T; simpl in H9; omega.
  - apply validate_read_unc; auto.
  - apply lock_unc; auto.
    intros t'; generalize (H3 t'); intros X; destruct X.
    now left.
    right; contradict H4.
    destruct H4 as [V [I NI]]; exists V; split.
    destruct I as [I|I]; auto.
    inversion I; subst.
    inversion U; [cbn in *; contradiction|].
    simpl in H6; cln; omega.
    contradict NI; now right.
  - apply complete_unc; auto.
  - apply unlock_unc; auto.
Qed.

Lemma swap_forward_all_committed tid1 tid2 a1 a2 t1 t2:
  sto_trace (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) ->
  all_committed (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) ->
  action_phase a1 < 3 ->
  tid1 <> tid2 ->
  sto_trace (t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
Proof.
  intros T1 A AP N.
  generalize (trace_app _ _ T1); intros TB.
  assert (unconflicted ((tid2, a2) :: (tid1, a1) :: t2)). {
    apply committable_unconflicted; auto.
    now exists t1.
  }
  apply sto_trace_permutation_app with (t1:=(tid2,a2)::(tid1,a1)::t2).
  auto.
  apply swap_forward_unconflicted; auto.
  apply trace_same_end_state_unconflicted_forward; auto.
Qed.

Lemma swap_backward_all_committed tid1 tid2 a1 a2 t1 t2:
  sto_trace (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) ->
  all_committed (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) ->
  3 <= action_phase a2 ->
  tid1 <> tid2 ->
  sto_trace (t1 ++ (tid1, a1) :: (tid2, a2) :: t2).
Proof.
  intros T1 A AP N.
  generalize (trace_app _ _ T1); intros TB.
  assert (unconflicted ((tid2, a2) :: (tid1, a1) :: t2)). {
    apply committable_unconflicted; auto.
    now exists t1.
  }
  apply sto_trace_permutation_app with (t1:=(tid2,a2)::(tid1,a1)::t2).
  auto.
  apply swap_backward_committing; auto.
  apply in_all_committed with (tid0:=tid2) (t:=t1 ++ (tid2, a2) :: (tid1, a1) :: t2); auto.
  apply in_or_app; right; now left.
  assert (action_phase a1 <= 4). {
    apply in_all_committed with (tid0:=tid1) (t:=t1++(tid2, a2)::(tid1, a1)::t2); auto.
    apply in_or_app; right; right; now left.
  }
  omega.
  apply trace_same_end_state_unconflicted_backward; auto.
Qed.



(* NB this function can actually move sequential points around!
   It's only correct if there are no aborted txns. *)

Definition swappable (tid2:tid) a2 (tid1:tid) a1 :=
  if Nat.eq_dec tid1 tid2
  then false
  else if (action_phase a1 <? 3) || (3 <=? action_phase a2)
       then match a1, a2 with
            | seq_point, seq_point => false
            | _, _ => true
            end
       else false.

Lemma swappable_iff tid2 a2 tid1 a1:
  swappable tid2 a2 tid1 a1 = true <->
  (a2 <> seq_point \/ a1 <> seq_point)
  /\ tid1 <> tid2
  /\ (action_phase a1 < 3 \/ 3 <= action_phase a2).
Proof.
  split; intros; unfold swappable in *.
  - destruct (Nat.eq_dec tid1 tid2); [discriminate|].
    remember ((action_phase a1 <? 3) || (3 <=? action_phase a2)) as X.
    destruct X; [|discriminate].
    split; [|split].
    + destruct a1; destruct a2; try discriminate.
      all: try now left.
      all: try now right.
    + assumption.
    + symmetry in HeqX.
      rewrite orb_true_iff in HeqX; destruct HeqX; [left|right].
      now rewrite <- Nat.ltb_lt.
      now rewrite <- Nat.leb_le.
  - destruct H as [A [B C]].
    destruct (Nat.eq_dec tid1 tid2); [congruence|].
    destruct C as [C | C];
      [ rewrite <- Nat.ltb_lt in C | rewrite <- Nat.leb_le in C ];
      rewrite C; try rewrite orb_true_r; cbn.
    all: destruct a1; destruct a2; try reflexivity.
    all: intuition.
Qed.


Definition example_txn:=
  [ (2, commit_done_txn);
      (2, complete_write_item 0 1);
      (2, commit_txn);
      (2, validate_read_item 0 0);
      (2, seq_point);
      (2, lock_write_item 0);
      (2, try_commit_txn);
      (2, write_item 0 4);
      (2, read_item 0 0);
      (2, start_txn);
      (1, commit_done_txn);
      (1, commit_txn);
      (1, validate_read_item 0 0);
      (1, seq_point);
      (1, try_commit_txn);
      (1, read_item 0 0);
      (1, start_txn)].

Definition example_txn2:=
  [ (3, commit_done_txn);
      (3, commit_txn);
      (3, validate_read_item 0 1);
      (3, seq_point);
      (3, try_commit_txn);
      (3, read_item 0 1);
      (3, start_txn);
      (1, abort_txn);
      (1, validate_read_item 0 1);
      (1, try_commit_txn);
      (2, commit_txn);
      (2, complete_write_item 0 1);
      (2, commit_txn);
      (2, validate_read_item 0 0);
      (2, seq_point);
      (2, lock_write_item 0);
      (2, try_commit_txn);
      (2, write_item 0 4);
      (1, read_item 0 0);
      (2, read_item 0 0);
      (2, start_txn);
      (1, start_txn)].


Definition example_txn3 :=
  [  (3, commit_done_txn);
     (3, commit_txn);
     (3, validate_read_item 0 2);
     (3, seq_point);
     (3, try_commit_txn);
     (3, read_item 0 2);
     (2, commit_done_txn);
     (2, complete_write_item 0 2);
     (2, commit_txn);
     (3, start_txn);
     (1, commit_done_txn);
     (2, seq_point);
     (2, lock_write_item 0);
     (1, complete_write_item 0 1);
     (1, commit_txn);
     (1, seq_point);
     (1, lock_write_item 0);
     (2, try_commit_txn);
     (2, write_item 0 0);
     (1, try_commit_txn);
     (1, write_item 0 1);
     (1, start_txn);
     (2, start_txn) ].


Inductive swap_permutation : relation trace :=
| swap_perm_nil : swap_permutation [] []
| swap_perm_skip : forall x t1 t2,
    swap_permutation t1 t2 ->
    swap_permutation (x::t1) (x::t2)
| swap_perm_swap : forall tid2 a2 tid1 a1 t,
    swappable tid2 a2 tid1 a1 = true ->
    swap_permutation ((tid2, a2) :: (tid1, a1) :: t) ((tid1, a1) :: (tid2, a2) :: t)
| swap_perm_trans : forall t1 t2 t3,
    swap_permutation t1 t2 ->
    swap_permutation t2 t3 ->
    swap_permutation t1 t3.

Lemma swap_permutation_permutation {t1 t2}:
  swap_permutation t1 t2 ->
  Permutation t1 t2.
Proof.
  intros SP; induction SP; try constructor; auto.
  now apply perm_trans with (l':=t2).
Qed.

Lemma swap_permutation_refl t:
  swap_permutation t t.
Proof.
  induction t; now constructor.
Qed.

Lemma swap_permutation_tid_eq t1 t2 tid:
  swap_permutation t1 t2 ->
  filter_tid tid t1 = filter_tid tid t2.
Proof.
  intros SP; induction SP; auto.
  - destruct x; cbn; destruct (Nat.eq_dec tid t); now rewrite IHSP.
  - cbn; destruct (Nat.eq_dec tid tid2); destruct (Nat.eq_dec tid tid1); auto.
    rewrite <- e in *; rewrite <- e0 in *; unfold swappable in H; cln; discriminate.
  - congruence.
Qed.

Lemma swap_permutation_app_head {t1 t2} l:
  swap_permutation t1 t2 ->
  swap_permutation (l ++ t1) (l ++ t2).
Proof.
  induction l; auto; intros.
  rewrite <- app_comm_cons; apply swap_perm_skip; now apply IHl.
Qed.

Lemma swap_permutation_app_tail {t1 t2} l:
  swap_permutation t1 t2 ->
  swap_permutation (t1 ++ l) (t2 ++ l).
Proof.
  intros T; induction T.
  now apply swap_permutation_refl.
  repeat rewrite <- app_comm_cons; now apply swap_perm_skip.
  repeat rewrite <- app_comm_cons; now apply swap_perm_swap.
  now apply swap_perm_trans with (t2:=t2++l).
Qed.

Lemma swap_permutation_app {t1 t2 t3 t4}:
  swap_permutation t1 t2 ->
  swap_permutation t3 t4 ->
  swap_permutation (t1 ++ t3) (t2 ++ t4).
Proof.
  intros T; induction T; intros X; auto.
  all: repeat rewrite <- app_comm_cons.
  apply swap_perm_skip; now apply IHT.
  apply swap_perm_trans with (t2:=((tid2, a2)::(tid1,a1)::t++t4)).
  repeat rewrite app_comm_cons; now apply swap_permutation_app_head.
  now apply swap_perm_swap.
  apply swap_perm_trans with (t2:=t2 ++ t3).
  now apply swap_permutation_app_tail.
  now apply IHT2.
Qed.

Lemma swap_permutation_phase {tid t1 t2}:
  swap_permutation t1 t2 ->
  tid_phase tid t1 = tid_phase tid t2.
Proof.
  intros SP; induction SP; auto.
  - destruct x; cbn; destruct (Nat.eq_dec tid t); auto.
  - apply swappable_iff in H; destruct H as [I1 [I2 I3]].
    cbn; destruct (Nat.eq_dec tid tid2); destruct (Nat.eq_dec tid tid1); congruence.
  - congruence.
Qed.

Lemma swap_permutation_last_write {t1 t2}:
  swap_permutation t1 t2 ->
  forall tid ad, tid_last_write tid ad t1 = tid_last_write tid ad t2.
Proof.
  intros SP; induction SP; intros tid; auto.
  - intros ad; destruct x; cbn; destruct (Nat.eq_dec tid t); destruct a; auto.
    all: destruct (Nat.eq_dec ad ad0); auto.
  - apply swappable_iff in H; destruct H as [I1 [I2 I3]].
    cbn; destruct (Nat.eq_dec tid tid2); destruct (Nat.eq_dec tid tid1); congruence.
  - congruence.
Qed.

Lemma swap_permutation_trace t1 t2:
  swap_permutation t1 t2 ->
  sto_trace t1 ->
  unconflicted t1 ->
  no_aborted t1 ->
    sto_trace t2
    /\ unconflicted t2
    /\ (forall ad, locked_by ad t1 0 = locked_by ad t2 0)
    /\ (forall ad, write_version ad t1 = write_version ad t2).
Proof.
  intros SP T U NA; induction SP; auto.
  - generalize (trace_cons _ _ T); intros T1.
    generalize (unconflicted_cons _ _ U); intros U1.
    generalize (no_aborted_cons _ _ NA); intros NA1.
    generalize (IHSP T1 U1 NA1); intros X; destruct X as [T2 [U2 [L WV]]]; clear IHSP.
    assert (trace_same_end_state t1 t2) as Se. {
      split; [|split; [|split]]; auto.
      now apply swap_permutation_permutation.
      now apply swap_permutation_last_write.
    }
    destruct x; split; [| split; [| split]].
    apply sto_trace_permutation_cons with (t1:=t1); auto.
    apply unconflicted_permutation_cons with (t1:=t1); auto.
    intros ad; simpl; repeat rewrite L; auto.
    intros ad; simpl; repeat rewrite WV; auto.

  - rewrite swappable_iff in H.
    destruct H as [SS [ST SA]].
    assert (trace_same_end_state ((tid2, a2)::(tid1, a1)::t) ((tid1, a1)::(tid2, a2)::t)) as Sep. {
      destruct SA.
      now apply trace_same_end_state_unconflicted_forward.
      now apply trace_same_end_state_unconflicted_backward.
    }
    split; [| split; [| split]].

    + destruct SA.
      now apply swap_forward_unconflicted.
      apply swap_backward_committing; auto.
      apply (NA tid2 a2); now left.
      assert (action_phase a1 <= 4). {
        apply (NA tid1 a1); right; now left.
      }
      omega.
    + destruct SA.
      now apply unconflicted_unconflicted_forward.
      now apply unconflicted_unconflicted_backward.
    + destruct Sep as [Sep1 [Sep2 [Sep3 Sep4]]]; auto.
    + destruct Sep as [Sep1 [Sep2 [Sep3 Sep4]]]; auto.

  - generalize (IHSP1 T U NA); intros X2.
    destruct X2 as [T2 [U2 [L2 WV2]]]; clear IHSP1.
    assert (no_aborted t2) as NA2. {
      intros tid a I; apply (NA tid a).
      now apply (Permutation_in _ (Permutation_sym (swap_permutation_permutation SP1))).
    }
    generalize (IHSP2 T2 U2 NA2); intros X2.
    destruct X2 as [T3 [U3 [L3 WV3]]]; clear IHSP2.
    split; [| split; [| split]]; congruence.
Qed.

Inductive serial_trace : trace -> Prop :=
| serial_empty : serial_trace []
| serial_new: forall tid a t,
    serial_trace t ->
    tid_phase tid t = 0 ->
    serial_trace ((tid, a) :: t)
| serial_same: forall tid a1 a2 t,
    serial_trace ((tid, a2) :: t) ->
    serial_trace ((tid, a1) :: (tid, a2) :: t).

Lemma serial_cons x t:
  serial_trace (x :: t) ->
  serial_trace t.
Proof.
  intros Se; inversion Se; auto.
Qed.

Lemma serial_app_head_inv t1 t2:
  serial_trace (t1 ++ t2) ->
  serial_trace t2.
Proof.
  induction t1; cbn; auto.
  intros; apply serial_cons in H; auto.
Qed.


Lemma serial_trace_split tid t:
  serial_trace t ->
  sto_trace t ->
  tid_phase tid t > 0 ->
  exists t1 t2 t3,
    t = t1 ++ t2 ++ t3
    /\ tid_phase tid t1 = 0
    /\ (forall tid' a, In (tid', a) t2 -> tid = tid')
    /\ tid_phase tid t3 = 0
    /\ (forall tid' a a', In (tid', a) t1 -> ~ In (tid', a') t3).
Proof.
  intros Se; induction Se; intros T P.
  (* serial_empty *)
  cbn in P; omega.

  (* serial_new *)
  cbn in P.
  destruct (Nat.eq_dec tid tid0). {
    rewrite <- e in *; clear tid0 e.
    exists [], [(tid, a)], t.
    repeat split; cbn; auto.
    intros tx ax I; destruct I.
    now inversion H0.
    contradiction.
  }

  apply (IHSe (trace_cons _ _ T)) in P.
  destruct P as [t1 [t2 [t3 [P1 [P2 [P3 [P4 P5]]]]]]].
  exists ((tid0, a) :: t1), t2, t3.
  repeat split; cbn; auto.
  now rewrite P1.
  now cln.
  intros tx ax ax' I; destruct I.
  inversion H0.
  enough (~ In (tx, ax') (t1 ++ t2 ++ t3)).
  contradict H1; apply in_or_app; right; apply in_or_app; now right.
  apply tid_phase_zero_not_in.
  rewrite <- H2; rewrite <- P1; auto.
  now apply (P5 _ ax).

  (* serial_same *)
  assert (tid_phase tid ((tid0, a2) :: t) > 0) as P2. {
    cbn in *.
    destruct (Nat.eq_dec tid tid0); auto.
    destruct a2; cbn; omega.
  }
  apply (IHSe (trace_cons _ _ T)) in P2.
  destruct P2 as [t1 [t2 [t3 [P1 [P2 [P3 [P4 P5]]]]]]].
  destruct (Nat.eq_dec tid tid0). {
    rewrite <- e in *; clear tid0 e.
    exists [], ((tid, a1) :: t2), t3.
    assert (t1 = []) as L. {
      destruct t1; auto.
      rewrite <- app_comm_cons in P1; inversion P1.
      rewrite <- H0 in P2; cbn in P2; cln.
      destruct a2; cbn in P2; omega.
    }
    repeat split; cbn; auto.
    rewrite L in *; cbn in *; rewrite P1; auto.
    intros tx ax I; destruct I.
    now inversion H.
    now apply (P3 _ ax).
  }
  destruct t1. {
    exists [], [], ((tid0, a1) :: t3).
    assert (t2 = []) as L. {
      destruct t2; auto.
      cbn in P1; inversion P1.
      assert (In (tid0, a2) (p :: t2)). {
        rewrite H0; now left.
      }
      apply P3 in H.
      congruence.
    }
    rewrite L in *; cbn in P1; rewrite P1.
    repeat split; cbn; auto.
    now cln.
  }
  {
    exists ((tid0, a1) :: p :: t1), t2, t3.
    rewrite P1; repeat rewrite <- app_comm_cons.
    repeat split; cbn; auto.
    cln; apply P2.
    intros tx ax ay I; repeat destruct or I.
    inversion I.
    apply (P5 _ a2).
    inversion P1; rewrite H0; now left.
    apply (P5 _ ax).
    rewrite I; now left.
    apply (P5 _ ax).
    now right.
  }
Qed.

Lemma swap_permutation_backward tid a t1 t2:
  a <> seq_point ->
  3 <= action_phase a ->
  (forall a', ~ In (tid, a') t1) ->
  swap_permutation ((tid, a) :: t1 ++ t2) (t1 ++ (tid, a) :: t2).
Proof.
  induction t1; cbn; intros NS P P1.
  apply swap_permutation_refl.
  assert (swap_permutation ((tid, a) :: t1 ++ t2) (t1 ++ (tid, a) :: t2)). {
    apply IHt1; auto.
    intros a' I.
    apply (P1 a'); now right.
  }
  apply swap_perm_skip with (x:=a0) in H.
  apply swap_perm_trans with (t2:=a0::(tid,a)::t1++t2); auto.
  destruct a0; apply swap_perm_swap.
  destruct (Nat.eq_dec tid t).
  contradict P1.
  intros A; apply (A a0); left; rewrite e; auto.
  unfold swappable; do 3 cln.
  destruct a0; auto.
  destruct a; auto.
Qed.

Lemma swap_permutation_forward_once tid a t1 t2:
  action_phase a < 3 ->
  (forall a', ~ In (tid, a') t1) ->
  swap_permutation (t1 ++ (tid, a) :: t2) ((tid, a) :: t1 ++ t2).
Proof.
  induction t1; cbn; intros NS P1.
  apply swap_permutation_refl.
  assert (swap_permutation (t1 ++ (tid, a) :: t2) ((tid, a) :: t1 ++ t2)). {
    apply IHt1; auto.
    intros a' I.
    apply (P1 a'); now right.
  }
  apply swap_perm_skip with (x:=a0) in H.
  apply swap_perm_trans with (t2:=a0::(tid,a)::t1++t2); auto.
  destruct a0; apply swap_perm_swap.
  destruct (Nat.eq_dec tid t).
  contradict P1.
  intros A; apply (A a0); left; rewrite e; auto.
  unfold swappable; do 3 cln.
  destruct a; auto.
  cbn in NS; omega.
Qed.

Lemma swap_permutation_forward tid t1 t2 t3:
  (forall a', ~ In (tid, a') t1) ->
  (forall tid' a', In (tid', a') t2 -> tid = tid' /\ action_phase a' < 3) ->
  swap_permutation (t1 ++ t2 ++ t3) (t2 ++ t1 ++ t3).
Proof.
  induction t2; cbn; intros N1 N2.
  apply swap_permutation_refl.
  assert (swap_permutation (t1 ++ t2 ++ t3) (t2 ++ t1 ++ t3)). {
    apply IHt2; auto.
  }
  apply swap_perm_skip with (x:=a) in H.
  apply swap_perm_trans with (t2:=a::t1++t2++t3); auto.
  destruct a; apply swap_permutation_forward_once.
  generalize (N2 t a); intuition.
  intros a' I; apply (N1 a').
  enough (t = tid).
  rewrite <- H0; auto.
  generalize (N2 t a); intuition.
Qed.

Lemma trace_nonzero_segment tid t1 t2:
  sto_trace t1 ->
  tid_phase tid t2 = 0 ->
  (forall x, In x t2 -> In x t1) ->
  (forall a, ~ In (tid, a) t2).
Proof.
  revert t1; induction t2; intros t1 T P X aa I.
  destruct I.
  destruct a as [tid' a].
  assert (action_phase a > 0). {
    apply (trace_no_dummy tid' _ t1); auto.
    apply X; now left.
  }
  assert (forall a, ~ In (tid, a) t2). {
    apply IHt2 with (t1:=t1); auto.
    cbn in P; destruct (Nat.eq_dec tid tid').
    omega.
    auto.
    intros x II; apply X; now right.
  }
  destruct I.
  inversion H1; subst.
  simpl in P; cln.
  omega.
  apply (H0 aa H1).
Qed.

Lemma serial_trace_swap tid2 t1 t2 t3:
  serial_trace (t1 ++ t2 ++ t3) ->
  tid_phase tid2 t1 = 0 ->
  tid_phase tid2 t3 = 0 ->
  (forall tid a, In (tid, a) t2 -> tid2 = tid) ->
  (forall tid a a', In (tid, a) t1 -> ~ In (tid, a') t3) ->
  serial_trace (t2 ++ t1 ++ t3).
Proof.
  induction t1; cbn in *; auto.
  intros Se P1 P3 P2 X13.
  destruct a; destruct (Nat.eq_dec tid2 t); auto.
  destruct a; cbn in P1; omega.
  assert (serial_trace (t2 ++ t1 ++ t3)) as Se2. {
    apply IHt1.
    apply (serial_cons _ _ Se).
    auto.
    auto.
    apply P2.
    intros tx ax ay I.
    apply (X13 tx ax ay); now right.
  }
  clear IHt1.
  enough (serial_trace ((t, a) :: t1 ++ t3)). {
    clear Se2 Se; induction t2; auto.
    assert (serial_trace (t2 ++ (t, a) :: t1 ++ t3)). {
      apply IHt2.
      intros tt aa I; apply (P2 tt aa); now right.
    }
    destruct a0.
    assert (tid2 = t0). {
      apply P2 with (a:=a0); now left.
    }
    rewrite <- H1 in *; clear t0 H1.
    destruct t2; cbn in *.
    - apply serial_new; auto.
      apply tid_phase_not_in_zero.
      intros aa I.
      destruct I.
      inversion H1.
      congruence.
      apply in_app_or in H1; destruct or H1.
      apply tid_phase_zero_not_in with (a:=aa) in P1; contradiction.
      apply tid_phase_zero_not_in with (a:=aa) in P3; contradiction.
    - destruct p.
      assert (tid2 = t0) as e. {
        apply P2 with (a:=a1); right; now left.
      }
      rewrite <- e in *; clear t0 e.
      now apply serial_same.
  }
  apply serial_app_head_inv in Se2.
  destruct (Nat.eq_dec (tid_phase t t1) 0). {
    apply serial_new; auto.
    rewrite tid_phase_zero_app_skip; auto.
    apply tid_phase_not_in_zero; intros aa.
    apply (X13 t a aa); now left.
  }
  destruct t1.
  cbn in n0; omega.
  destruct p; cbn in *.
  destruct (Nat.eq_dec t t0).
  rewrite <- e in *; clear t0 e.
  apply serial_same; auto.
  inversion Se; try congruence.
  contradict n0.
  apply tid_phase_not_in_zero; intros aa.
  apply tid_phase_zero_not_in with (a:=aa) in H3.
  contradict H3.
  right; apply in_or_app; now left.
Qed.
    

Lemma serial_swap_permutation' t:
  sto_trace t ->
  unconflicted t ->
  no_aborted t ->  
  exists tt,
    swap_permutation t tt
    /\ serial_trace tt.
Proof.
  induction t; intros T U NA.
  exists []; split; constructor.
  generalize (IHt (trace_cons _ _ T) (unconflicted_cons _ _ U) (no_aborted_cons _ _ NA)); intros X.
  destruct X as [tt [SW SE]].
  destruct a as [tid a].

  destruct (action_dec a start_txn). {
    rewrite e in *; exists ((tid, start_txn) :: tt); split.
    now apply swap_perm_skip.
    apply serial_new; auto.
    rewrite <- (swap_permutation_phase SW).
    now inversion T.
  }

  assert (tid_phase tid tt > 0) as TNZ. {
    rewrite <- (swap_permutation_phase SW).
    inversion T; congruence || omega.
  }
  assert (sto_trace tt) as T2. {
    generalize (swap_permutation_trace t tt SW (trace_cons _ _ T) (unconflicted_cons _ _ U) (no_aborted_cons _ _ NA)); intros; intuition.
  }

  assert ((action_phase a < 3 \/ a = seq_point)
          \/ (a <> seq_point /\ 3 <= action_phase a)) as A. {
    destruct a; cbn.
    all: try solve [ left; left; omega ].
    left; right; auto.
    all: solve [ right; split; [ congruence | omega ]].
  }
  generalize (serial_trace_split tid tt SE T2 TNZ); intros G.
  destruct G as [t1 [t2 [t3 [G1 [G2 [G3 [G4 G5]]]]]]].
  destruct A as [A|A].

  exists ((tid, a) :: t2 ++ t1 ++ t3).
  split.
  {
    apply swap_perm_skip.
    apply swap_perm_trans with (t2:=tt); auto.
    rewrite G1.
    apply swap_permutation_forward with (tid0:=tid).
    apply (trace_nonzero_segment tid tt t1); auto.
    intros x I; rewrite G1; apply in_or_app; now left.
    intros tid' a' I.
    split; [ apply (G3 _ a' I) | ].
    assert (In (tid', a') t).
    apply Permutation_in with (l:=tt).
    apply Permutation_sym; now apply swap_permutation_permutation.
    rewrite G1; apply in_or_app; right; apply in_or_app; now left.
    rewrite <- (G3 tid' a' I) in *.
    destruct A.
    enough (action_phase a' <= 2) by omega.
    assert (In (tid, a') ((tid, a) :: t)) by (now right).
    apply phase_increase_in in H1.
    cbn in H1; cln.
    omega.
    auto.

    rewrite H0 in *.
    inversion T.
    enough (action_phase a' <= 2) by omega.
    rewrite <- H3.
    apply phase_increase_in.
    apply (trace_cons _ _ T).
    auto.
  }
  {
    rewrite G1 in SE.
    clear IHt T U NA tt SW n TNZ T2 A G1.
    enough (serial_trace (t2 ++ t1 ++ t3)). {
      destruct t2.    
      cbn in *; apply serial_new; auto.
      now rewrite tid_phase_zero_app_skip.
      destruct p; cbn in *.
      assert (tid = t0) as e. {
        apply G3 with (a:=a0); now left.
      }
      rewrite <- e in *; clear e.
      apply serial_same; auto.
    }
    apply serial_trace_swap with (tid2:=tid); auto.
  }

  exists (t1 ++ (tid, a) :: t2 ++ t3).
  split.
  {
    apply swap_perm_trans with (t2:=(tid, a)::tt); auto.
    apply swap_perm_skip; auto.
    rewrite G1.
    apply swap_permutation_backward; auto.
    intuition.
    intuition.
    apply (trace_nonzero_segment tid tt t1); auto.
    intros x II; rewrite G1.
    apply in_or_app; now left.
  }
  {
    rewrite G1 in SE.
    clear IHt T U NA tt SW n TNZ T2 A G1.
    induction t1.
    - cbn in *; clear G2.
      destruct t2.
      + apply serial_new; auto.
      + destruct p.
        assert (tid = t0) as e by (apply (G3 _ a0); now left).
        rewrite <- e in *; cbn in *.
        apply serial_same; auto.
    - cbn in *.
      destruct t1; destruct a0.
      + cbn in *; apply serial_new; auto.
        apply IHt1.
        apply (serial_cons _ _ SE).
        auto.
        intros; contradiction.
        destruct (Nat.eq_dec tid t0).
        destruct a0; cbn in G2; omega.
        cbn; cln.
        rewrite (tid_phase_zero_app_skip).
        apply tid_phase_not_in_zero.
        intros a1; apply (G5 t0 a0 a1); now left.
        apply tid_phase_not_in_zero.
        intros a1 I; apply G3 in I; congruence.
      + destruct p; cbn in *.
        destruct (Nat.eq_dec tid t0).
        destruct a0; cbn in G2; omega.
        destruct (Nat.eq_dec tid t4).
        destruct a1; cbn in G2; omega.
        inversion SE.
        * apply serial_new.
          apply IHt1; auto.
          intros tx ax ay I.
          apply (G5 _ ax); intuition.
          apply tid_phase_not_in_zero; intros a3 I.
          apply tid_phase_zero_not_in with (a:=a3) in H3.
          contradict H3.
          destruct I; [now left|right].
          apply in_app_or in H3; destruct or H3; [ apply in_or_app; intuition | ].
          destruct H3; try congruence.
          apply in_app_or in H3; destruct or H3; [ apply in_or_app; intuition | ].
          apply in_or_app; right; apply in_or_app; intuition.
        * apply serial_same.
          apply IHt1; auto.
          intros tx ax ay I.
          apply (G5 _ ax); intuition.
  }
Qed.

Lemma serial_swap_permutation t:
  sto_trace t ->
  unconflicted t ->
  no_aborted t ->  
  exists tt,
    swap_permutation t tt
    /\ sto_trace tt
    /\ unconflicted tt
    /\ no_aborted tt
    /\ serial_trace tt.
Proof.
  intros T U N.
  generalize (serial_swap_permutation' t T U N).
  intros X; destruct X as [tt [SW Se]].
  generalize (swap_permutation_trace t tt SW T U N).
  intros X; destruct X as [T2 [U2 [L2 WV2]]].
  exists tt; repeat split; auto.
  intros tid a I.
  apply (N tid).
  apply Permutation_in with (l:=tt); auto.
  apply Permutation_sym; now apply swap_permutation_permutation.
Qed.



(** BELOW HERE LESS INTERESTING *******************************************)
Lemma swap_permutation_refl_skip x t:
  (forall t2, swap_permutation (x :: t) t2 -> x :: t = t2) ->
  forall t2, swap_permutation t t2 -> t = t2.
Proof.
  intros.
  assert (x :: t = x :: t2 -> t = t2). {
    intros; inversion H1; auto.
  }
  apply H1.
  apply H.
  now constructor.
Qed.

Lemma swap_permutation_fixpoint_serial t:
  sto_trace t ->
  (forall t2, swap_permutation t t2 -> t = t2) ->
  serial_trace t.
Proof.
  induction t; intros T S.
  now apply serial_empty.
  assert (forall t2, swap_permutation t t2 -> t = t2)
    as S2 by (now apply (swap_permutation_refl_skip _ _ S)).
  assert (serial_trace t) as ST by (now apply (IHt (trace_cons _ _ T))).
  destruct a as [tid a].
  destruct (action_dec a start_txn).
  rewrite e in *; inversion T; now apply serial_new.
  assert (tid_phase tid t > 0) as PNZ. {
    destruct a; try congruence; inversion T; omega.
  }
  destruct t; [ cbn in PNZ; omega | ].
  destruct p as [tid' a'].
  destruct (Nat.eq_dec tid tid'); [ rewrite e in *; now apply serial_same | ].

  enough (exists tt, swap_permutation ((tid, a) :: (tid', a') :: t) tt /\ tt <> (tid, a) :: (tid', a') :: t).
  destruct H as [tt [PP XX]].
  apply S in PP.
  congruence.

  assert ((action_phase a < 3 \/ a = seq_point)
          \/ (a <> seq_point /\ 3 <= action_phase a)) as A. {
    destruct a; cbn.
    all: try solve [ left; left; omega ].
    left; right; auto.
    all: solve [ right; split; [ congruence | omega ]].
  }

  destruct A.

  - assert (exists t1 tidx ax ay t2,
               (tid', a') :: t = t1 ++ (tidx, ax) :: (tid, ay) :: t2
               /\ tidx <> tid
               /\ tid_phase tid t1 = 0) as A. {
      apply (@trace_find_previous _ a); auto.
    }
    destruct A as [t1 [tidx [ax [ay [t2 [E [N P]]]]]]].
    assert (tid_phase tid ((tid', a') :: t) = action_phase ay) as TP. {
      rewrite E in *.
      rewrite tid_phase_zero_app_skip; auto.
      cbn; do 2 cln; auto.
    }
    assert (action_phase ay < 3) as AYP. {
      destruct H.
      - enough (tid_phase tid ((tid,a) :: (tid',a') :: t) >= action_phase ay).
        cbn in H0; cln; omega.
        apply phase_increase_in; auto.
        rewrite E; right.
        apply in_or_app; right; right; now left.
      - rewrite H in *; clear H.
        inversion T.
        rewrite H1 in TP; omega.
    }
    enough (swap_permutation (t1 ++ (tidx, ax) :: (tid, ay) :: t2)
                             (t1 ++ (tid, ay) :: (tidx, ax) :: t2)).
    rewrite <- E in H0; apply S2 in H0; rewrite E in H0.
    apply app_inv_head in H0.
    inversion H0; congruence.
    apply swap_permutation_app_head.
    apply swap_perm_swap.
    unfold swappable.
    do 3 cln.
    destruct ay; auto.
    cbn in AYP; omega.

  - destruct H.
    assert (swappable tid a tid' a' = true) as Sw. {
      unfold swappable.
      do 3 cln.
      destruct a'; auto.
      destruct a; auto; cbn in l; omega.
    }
    exists ((tid', a') :: (tid, a) :: t); split; try congruence.
    now apply swap_perm_swap.
Qed.






Inductive subl {A:Type} : relation (list A) :=
| subl_nil : subl [] []
| subl_skip : forall x l1 l2,
    subl l1 l2 ->
    subl (x :: l1) (x :: l2)
| subl_cons : forall x l1 l2,
    subl l1 l2 ->
    subl l1 (x :: l2).
Hint Constructors subl.

Lemma subl_refl {A:Type} (l:list A):
  subl l l.
Proof.
  induction l; auto.
Qed.

Lemma subl_empty {A:Type} (l:list A):
  subl [] l.
Proof.
  induction l; auto.
Qed.

Lemma subl_add_head {A:Type} (l1 l2 h:list A):
  subl l1 l2 ->
  subl l1 (h ++ l2).
Proof.
  induction h; intros; try rewrite <- app_comm_cons; auto.
Qed.

Lemma subl_add_middle {A:Type} (l1 l2a l2b:list A) x:
  subl l1 (l2a ++ l2b) ->
  subl l1 (l2a ++ x :: l2b).
Proof.
  revert l1 l2b; induction l2a; cbn; auto.
  intros; destruct l1; [ apply subl_empty | ].
  inversion H.
  apply subl_skip; auto.
  apply subl_cons; auto.
Qed.

Lemma subl_add_tail {A:Type} (l1 l2 t:list A):
  subl l1 l2 ->
  subl l1 (l2 ++ t).
Proof.
  induction t; intros; try rewrite app_nil_r; auto.
  apply subl_add_middle; auto.
Qed.

Lemma subl_split {A:Type} x (l1 l2:list A):
  subl (x :: l1) l2 ->
  exists l2a l2b, l2 = l2a ++ x :: l2b
                  /\ subl l1 l2b.
Proof.
  remember (x :: l1) as xl1; intros S; revert x l1 Heqxl1.
  induction S; intros.
  congruence.
  inversion Heqxl1; subst.
  exists [], l2; intuition.
  apply IHS in Heqxl1.
  destruct Heqxl1 as [l2a [l2b [H1 H2]]].
  exists (x::l2a), l2b.
  rewrite H1; intuition.
Qed.

Lemma subl_trans {A:Type} (l1 l2 l3:list A):
  subl l1 l2 ->
  subl l2 l3 ->
  subl l1 l3.
Proof.
  intros S1; revert l3; induction S1; intros; auto.
  all: apply subl_split in H.
  all: destruct H as [l2a [l2b [H1 H2]]].
  all: rewrite H1 in *; clear H1.
  all: apply subl_add_head.
  1: apply subl_skip.
  2: apply subl_cons.
  all: apply IHS1; auto.
Qed.
  
Lemma subl_incl {A:Type} {l1 l2:list A}:
  subl l1 l2 ->
  incl l1 l2.
Proof.
  intros S; induction S.
  apply incl_refl.
  intros y I; destruct I; [ now left | right; now apply IHS ].
  intros y I; right; now apply IHS.
Qed.

Lemma subl_app {A:Type} (l1 l2 l3:list A):
  subl l2 (l1 ++ l2 ++ l3).
Proof.
  apply subl_add_head; apply subl_add_tail; now apply subl_refl.
Qed.

Function swap_once (t:trace) { measure length t } :=
  match t with
  | (tid2, a2) :: (tid1, a1) :: t' =>
    if swappable tid2 a2 tid1 a1
    then (tid1, a1) :: swap_once ((tid2, a2) :: t')
    else (tid2, a2) :: swap_once ((tid1, a1) :: t')
  | _ => t
  end.
Proof.
  all: intros; cbn; try apply lt_n_S; omega.
Defined.

Fixpoint swap_n t n :=
  match n with
  | 0 => t
  | S n => swap_once (swap_n t n)
  end.

Lemma swap_once_permutation t:
  swap_permutation t (swap_once t).
Proof.
  functional induction (swap_once t).
  - apply swap_perm_trans with (t2:=(tid1, a1) :: (tid2, a2) :: t');
    now constructor.
  - now constructor.
  - apply swap_permutation_refl.
Qed.

Lemma swap_n_permutation t n:
  swap_permutation t (swap_n t n).
Proof.
  induction n; simpl.
  apply swap_permutation_refl.
  generalize (swap_once_permutation (swap_n t n)) as PE; intros PE.
  now apply swap_perm_trans with (t2:=(swap_n t n)).
Qed.



Lemma swap_once_trace t:
  sto_trace t ->
  unconflicted t ->
  no_aborted t ->
  sto_trace (swap_once t).
Proof.
  intros T U NA.
  generalize (swap_once_permutation t); intros SP.
  generalize (swap_permutation_trace _ _ SP T U NA); intros H; intuition.
Qed.

Lemma swap_n_trace t n:
  sto_trace t ->
  unconflicted t ->
  no_aborted t ->
  sto_trace (swap_n t n).
Proof.
  intros T U NA.
  generalize (swap_n_permutation t n); intros SP.
  generalize (swap_permutation_trace _ _ SP T U NA); intros H; intuition.
Qed.

  

Lemma swap_once_cons x t:
  swap_once (x::t) = x :: t ->
  swap_once t = t.
Proof.
  revert x; induction t; intros; cbn; auto.
  destruct x; destruct a.
  rewrite swap_once_equation in H.
  remember (swappable t0 a0 t1 a) as s; destruct s.
  inversion H; subst; unfold swappable in Heqs.
  destruct (Nat.eq_dec t0 t0); [ discriminate | congruence ].
  inversion H; rewrite H1; auto.
Qed.

Lemma swap_once_app t1 tid2 a2 tid1 a1 t2:
  swap_once (t1 ++ (tid2, a2) :: (tid1, a1) :: t2) =
  t1 ++ (tid2, a2) :: (tid1, a1) :: t2 ->
  swappable tid2 a2 tid1 a1 = false.
Proof.
  induction t1; intros; cbn in *.
  rewrite swap_once_equation in H.
  remember (swappable tid2 a2 tid1 a1) as s; destruct s; auto.
  inversion H.
  unfold swappable in *; subst.
  destruct (Nat.eq_dec tid2 tid2); congruence.
  apply swap_once_cons in H.
  now apply IHt1.
Qed.


Lemma rev_split {A:Type} (l:list A):
  l = [] \/ exists l1 a, l = l1 ++ [a].
Proof.
  induction l using rev_ind.
  now left.
  right; now exists l, x.
Qed.

Lemma trace_find_previous {tid2 a2 tid1 a1 t}:
  sto_trace ((tid2, a2) :: (tid1, a1) :: t) ->
  tid2 <> tid1 ->
  a2 <> start_txn ->
  exists t1 tidx ax a0 t2,
    (tid1, a1) :: t = t1 ++ (tidx, ax) :: (tid2, a0) :: t2
    /\ tidx <> tid2
    /\ tid_phase tid2 t1 = 0.
Proof.
  intros T NE A.
  assert (tid_phase tid2 t > 0). {
    inversion T; [ congruence | cbn in * .. ].
    all: destruct (Nat.eq_dec tid2 tid1); [ congruence | try omega ].
  }
  generalize (tid_phase_split tid2 t (tid_phase tid2 t) eq_refl H); intros X.
  destruct X as [t1 [aa [t2 [X1 [X2 X3]]]]].
  generalize (rev_split t1); intros X; destruct X as [X | [t1l [[tidl al] X]]].
  exists [], tid1, a1, aa, t2; rewrite X1, X; cbn; intuition.
  exists ((tid1, a1) :: t1l), tidl, al, aa, t2; rewrite X1, X; cbn.
  rewrite <- app_assoc; cbn.
  split; auto.
  destruct (Nat.eq_dec tid2 tid1); [congruence|].
  rewrite X in *; clear X.
  split.
  destruct (Nat.eq_dec tidl tid2). {
    rewrite e in *; clear e.
    rewrite X1 in T.
    do 2 apply trace_cons in T.
    generalize (tid_phase_zero_not_in _ _ X3); intros M.
    assert (~ In (tid2, al) (t1l ++ [(tid2, al)])) by (apply M).
    assert (In (tid2, al) (t1l ++ [(tid2, al)])) by (apply in_or_app; right; now left).
    contradiction.
  }
  auto.
  now apply tid_phase_zero_app in X3.
Qed.

Lemma swap_once_fixpoint_contents t:
  sto_trace t ->
  swap_once t = t ->
  serial_trace t.
Proof.
  induction t; intros T S.
  apply serial_empty.
  destruct a as [tid2 a2]; destruct t.
  apply serial_new; [ constructor | now cbn ].

  destruct p as [tid1 a1].

  assert (serial_trace ((tid1, a1) :: t)) as Se. {
    apply IHt.
    apply (trace_cons _ _ T).
    apply (swap_once_cons _ _ S).
  }
  
  destruct (Nat.eq_dec tid2 tid1).
  rewrite e; apply serial_same; auto.

  destruct (le_lt_dec 4 (action_phase a2)).
  assert (swappable tid2 a2 tid1 a1 = true) as St. {
    unfold swappable.
    destruct (Nat.eq_dec tid1 tid2); [congruence | ].
    assert (3 <= action_phase a2) as l2 by omega.
    rewrite (leb_correct _ _ l2).
    rewrite orb_true_r.
    destruct a1; auto.
    destruct a2; auto.
    cbn in l; omega.
  }
  rewrite swap_once_equation in S; rewrite St in S; inversion S; congruence.

  inversion T; rewrite <- H0 in *; try solve [ cbn in l; omega ].
  now apply serial_new.

  assert (read_item (write_version t0) <> start_txn) as NE by congruence.
  generalize (trace_find_previous T n NE); intros P;
    destruct P as [t1 [tidx [ax [aa [t2 [L1 [L2 L3]]]]]]].
  assert (swappable tidx ax tid2 aa = false). {
    rewrite L1 in *; rewrite app_comm_cons in *.
    now apply swap_once_app in S.
  }
  assert (action_phase aa < 3). {
    rewrite L1 in H2.
    rewrite tid_phase_zero_app_skip in H2; auto.
    simpl in H2; destruct (Nat.eq_dec tid2 tidx); destruct (Nat.eq_dec tid2 tid2); try congruence.
    omega.
    now rewrite L1 in H4.
  }
  unfold swappable in H5.
  destruct (Nat.eq_dec tid2 tidx); try congruence.
  replace (action_phase aa <? 3) with true in H5.
  rewrite orb_true_l in H5.
  destruct aa; try discriminate.
  cbn in H6; omega.
  symmetry; now rewrite Nat.ltb_lt.

  assert (write_item val <> start_txn) as NE by congruence.
  generalize (trace_find_previous T n NE); intros P;
    destruct P as [t1 [tidx [ax [aa [t2 [L1 [L2 L3]]]]]]].
  assert (swappable tidx ax tid2 aa = false). {
    rewrite L1 in *; rewrite app_comm_cons in *.
    now apply swap_once_app in S.
  }
  assert (action_phase aa < 3). {
    rewrite L1 in H1.
    rewrite tid_phase_zero_app_skip in H1; auto.
    simpl in H1; destruct (Nat.eq_dec tid2 tidx); destruct (Nat.eq_dec tid2 tid2); try congruence.
    omega.
    now rewrite L1 in H3.
  }
  unfold swappable in H4.
  destruct (Nat.eq_dec tid2 tidx); try congruence.
  replace (action_phase aa <? 3) with true in H4.
  rewrite orb_true_l in H4.
  destruct aa; try discriminate.
  cbn in *; omega.
  symmetry; now rewrite Nat.ltb_lt.

  assert (try_commit_txn <> start_txn) as NE by congruence.
  generalize (trace_find_previous T n NE); intros P;
    destruct P as [t1 [tidx [ax [aa [t2 [L1 [L2 L3]]]]]]].
  assert (swappable tidx ax tid2 aa = false). {
    rewrite L1 in *; rewrite app_comm_cons in *.
    now apply swap_once_app in S.
  }
  assert (action_phase aa < 3). {
    rewrite L1 in H1.
    rewrite tid_phase_zero_app_skip in H1; auto.
    simpl in H1; destruct (Nat.eq_dec tid2 tidx); destruct (Nat.eq_dec tid2 tid2); try congruence.
    omega.
    now rewrite L1 in H3.
  }
  unfold swappable in H4.
  destruct (Nat.eq_dec tid2 tidx); try congruence.
  replace (action_phase aa <? 3) with true in H4.
  rewrite orb_true_l in H4.
  destruct aa; try discriminate.
  cbn in *; omega.
  symmetry; now rewrite Nat.ltb_lt.

  assert (lock_write_item <> start_txn) as NE by congruence.
  generalize (trace_find_previous T n NE); intros P;
    destruct P as [t1 [tidx [ax [aa [t2 [L1 [L2 L3]]]]]]].
  assert (swappable tidx ax tid2 aa = false). {
    rewrite L1 in *; rewrite app_comm_cons in *.
    now apply swap_once_app in S.
  }
  assert (action_phase aa < 3). {
    rewrite L1 in H2.
    rewrite tid_phase_zero_app_skip in H2; auto.
    simpl in H2; destruct (Nat.eq_dec tid2 tidx); destruct (Nat.eq_dec tid2 tid2); try congruence.
    omega.
    now rewrite L1 in H5.
  }
  unfold swappable in H6.
  destruct (Nat.eq_dec tid2 tidx); try congruence.
  replace (action_phase aa <? 3) with true in H6.
  rewrite orb_true_l in H6.
  destruct aa; try discriminate.
  cbn in *; omega.
  symmetry; now rewrite Nat.ltb_lt.

  assert (seq_point <> start_txn) as NE by congruence.
  generalize (trace_find_previous T n NE); intros P;
    destruct P as [t1 [tidx [ax [aa [t2 [L1 [L2 L3]]]]]]].
  assert (swappable tidx ax tid2 aa = false). {
    rewrite L1 in *; rewrite app_comm_cons in *.
    now apply swap_once_app in S.
  }
  assert (action_phase aa < 3). {
    rewrite L1 in H2.
    rewrite tid_phase_zero_app_skip in H2; auto.
    simpl in H2; destruct (Nat.eq_dec tid2 tidx); destruct (Nat.eq_dec tid2 tid2); try congruence.
    omega.
    now rewrite L1 in H4.
  }
  unfold swappable in H5.
  destruct (Nat.eq_dec tid2 tidx); try congruence.
  replace (action_phase aa <? 3) with true in H5.
  rewrite orb_true_l in H5.
  destruct aa; try discriminate.
  cbn in *; omega.
  symmetry; now rewrite Nat.ltb_lt.

  assert (swappable tid2 (validate_read_item vers) tid1 a1 = true) as St. {
    unfold swappable.
    destruct (Nat.eq_dec tid1 tid2); [congruence | ].
    cbn; rewrite orb_true_r.
    destruct a1; auto.
  }
  rewrite swap_once_equation in S; rewrite St in S; inversion S; congruence.
Qed.


Fixpoint shuffle_tid_once tid (t:trace) :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then (tid', a) :: t'
    else match shuffle_tid_once tid t' with
         | (tid'', a') :: t'' =>
           if Nat.eq_dec tid tid''
           then (tid'', a') :: (tid', a) :: t''
           else t
         | [] => t
         end
  | [] => []
  end.

Lemma shuffle_tid_once_Permutation tid t:
  Permutation t (shuffle_tid_once tid t).
Proof.
  induction t; cbn; auto.
  destruct a as [tid' a]; destruct (Nat.eq_dec tid tid').
  apply Permutation_refl.
  remember (shuffle_tid_once tid t) as s; destruct s.
  apply Permutation_refl.
  destruct p as [tid'' a']; destruct (Nat.eq_dec tid tid'').
  apply perm_trans with (l':=(tid', a) :: (tid'', a') :: s).
  apply perm_skip; auto.
  apply perm_swap.
  apply Permutation_refl.
Qed.

Definition tid_phase_less tid (t:trace) n :=
  forall a,
    In (tid, a) t ->
    action_phase a < n.

Lemma trace_tid_phase_less tid (t:trace) n:
  sto_trace t ->
  tid_phase tid t < n ->
  tid_phase_less tid t n.
Proof.
  intros T P a I.
  apply phase_increase_in in I; auto.
  omega.
Qed.


Lemma shuffle_tid_once_swap_perm tid t:
  tid_phase_less tid t 3 ->
  swap_permutation t (shuffle_tid_once tid t).
Proof.
  induction t; cbn; intros PL.
  constructor.
  destruct a as [tid' a]; destruct (Nat.eq_dec tid tid').
  apply swap_permutation_refl.
  remember (shuffle_tid_once tid t) as s.
  destruct s.
  apply swap_permutation_refl.
  destruct p as [tid'' a']; destruct (Nat.eq_dec tid tid'');
    [ | apply swap_permutation_refl].
  apply swap_perm_trans with (t2:=(tid',a)::(tid'',a')::s).
  apply swap_perm_skip.
  apply IHt.
  intros ax I.
  apply PL; now right.
  rewrite <- e in *; clear e.
  apply swap_perm_swap.
  assert (action_phase a' < 3). {
    apply PL; right.
    apply Permutation_in with (l:=(tid, a') :: s).
    unfold Top.tid in *.
    rewrite Heqs; apply Permutation_sym; apply shuffle_tid_once_Permutation.
    now left.
  }
  unfold swappable.
  destruct (Nat.eq_dec tid tid'); try congruence.
  assert ((action_phase a' <? 3) = true) as LL by (now rewrite Nat.ltb_lt).
  rewrite LL; rewrite orb_true_l.
  destruct a'; auto.
  cbn in LL; discriminate.
Qed.


Fixpoint shuffle_tid_n tid t n :=
  match n, t with
  | S n, _ :: _ => match shuffle_tid_once tid t with
                   | p :: t' => p :: shuffle_tid_n tid t' n
                   | [] => []
                   end
  | _, _ => t
  end.

Lemma shuffle_tid_n_Permutation tid t n:
  Permutation t (shuffle_tid_n tid t n).
Proof.
  revert t; induction n; intros; cbn.
  apply Permutation_refl.
  destruct t; [ apply Permutation_refl | ].
  assert (Permutation (p :: t) (shuffle_tid_once tid (p :: t)))
    by (apply shuffle_tid_once_Permutation).
  remember (shuffle_tid_once tid (p :: t)) as s; destruct s.
  apply Permutation_sym in H; apply Permutation_nil_cons in H; contradiction.
  apply perm_trans with (l':=p0 :: s); auto.
Qed.
  
Lemma shuffle_tid_n_swap_perm tid t n:
  tid_phase_less tid t 3 ->
  swap_permutation t (shuffle_tid_n tid t n).
Proof.
  revert t; induction n; intros t PL; cbn.
  apply swap_permutation_refl.
  destruct t; [ constructor | ].
  remember (shuffle_tid_once tid (p :: t)) as s.
  destruct s.
  assert (Permutation (p :: t) (shuffle_tid_once tid (p :: t))). {
    apply shuffle_tid_once_Permutation.
  }
  rewrite <- Heqs in H.
  apply Permutation_sym in H; apply Permutation_nil_cons in H.
  contradiction.
  assert (swap_permutation (p :: t) (p0 :: s)). {
    rewrite Heqs; apply shuffle_tid_once_swap_perm; auto.
  }
  apply swap_perm_trans with (t2:=p0 :: s); auto.
  apply swap_perm_skip.
  apply IHn.
  intros ax I; apply PL.
  apply Permutation_in with (l:=p0 :: s).
  apply Permutation_sym.
  now apply swap_permutation_permutation.
  now right.
Qed.

Function swap_beta (t:trace) {measure length t} :=
  match t with
  | (tid, seq_point) :: t' =>
    let x := shuffle_tid_n tid t' (length t') in
    (tid, seq_point) :: swap_beta x
  | (tid2, a2) :: (tid1, a1) :: t' =>
    if swappable tid2 a2 tid1 a1
    then (tid1, a1) :: swap_beta ((tid2, a2) :: t')
    else (tid2, a2) :: swap_beta ((tid1, a1) :: t')
  | _ => t
  end.
Proof.
  all: intros; cbn; try apply lt_n_S; try omega.
  replace (length (shuffle_tid_n tid2 t' (length t'))) with (length t').
  omega.
  apply Permutation_length.
  apply shuffle_tid_n_Permutation.
Defined.

Fixpoint swap_beta_n t n :=
  match n with
  | 0 => t
  | S n => swap_beta_n (swap_beta t) n
  end.

Inductive seq_point_correct : trace -> Prop :=
| spc_nil : seq_point_correct []
| spc_action : forall tid a t,
    seq_point_correct t ->
    a <> seq_point ->
    seq_point_correct ((tid, a) :: t)
| spc_seq_point : forall tid t,
    seq_point_correct t ->
    tid_phase_less tid t 3 ->
    seq_point_correct ((tid, seq_point) :: t).

Lemma seq_point_correct_cons x t:
  seq_point_correct (x :: t) ->
  seq_point_correct t.
Proof.
  intros H; inversion H; auto.
Qed.

Lemma shuffle_tid_once_seq_point_correct tid t:
  seq_point_correct t ->
  seq_point_correct (shuffle_tid_once tid t).
Proof.
  induction t; intros.
  simpl; constructor.
  destruct a as [tid' a]; cbn.
  destruct (Nat.eq_dec tid tid'); auto.
  remember (shuffle_tid_once tid t) as s.
  destruct s; auto.
  destruct p as [tid'' a']; destruct (Nat.eq_dec tid tid''); auto.
  assert (seq_point_correct ((tid'', a') :: s)). {
    apply IHt.
    now apply seq_point_correct_cons in H.
  }
  assert (seq_point_correct ((tid', a) :: s)). {
    assert (seq_point_correct s) as H1 by (now apply seq_point_correct_cons in H0).
    destruct a.
    all: try solve [ apply spc_action; [ auto | congruence ]].
    apply spc_seq_point; auto.
    intros ax I.
    inversion H; try congruence.
    apply H5.
    apply Permutation_in with (l:=(tid'', a') :: s).
    apply Permutation_sym; rewrite Heqs; apply shuffle_tid_once_Permutation.
    now right.
  }
  destruct a'.
  all: try solve [ apply spc_action; [ auto | congruence ]].
  apply spc_seq_point; auto.
  intros ax I.
  inversion H0; try congruence.
  apply H5.
  destruct I; auto.
  congruence.
Qed.

Lemma shuffle_tid_n_seq_point_correct tid t n:
  seq_point_correct t ->
  seq_point_correct (shuffle_tid_n tid t n).
Proof.
  revert t; induction n; intros.
  cbn; auto.
  cbn; destruct t; auto.
  remember (shuffle_tid_once tid (p :: t)) as s; destruct s.
  constructor.
  assert (seq_point_correct (p0 :: s)). {
    rewrite Heqs.
    now apply shuffle_tid_once_seq_point_correct.
  }
  assert (seq_point_correct (shuffle_tid_n tid s n)). {
    apply IHn.
    now apply seq_point_correct_cons in H0.
  }
  destruct p0 as [tid' a]; destruct a.
  all: try solve [ apply spc_action; [ auto | congruence ]].
  apply spc_seq_point; auto.
  intros ax I.
  inversion H0; try congruence.
  apply H5.
  apply Permutation_in with (l:=(shuffle_tid_n tid s n)).
  apply Permutation_sym; apply shuffle_tid_n_Permutation.
  auto.
Qed.

Lemma swap_beta_permutation t:
  seq_point_correct t ->
  swap_permutation t (swap_beta t).
Proof.
  functional induction (swap_beta t); intros T.
  - apply swap_perm_skip.
    apply swap_perm_trans with (t2:=shuffle_tid_n tid0 t' (length t')).
    apply shuffle_tid_n_swap_perm.
    inversion T; try congruence; auto.
    apply IHt0.
    apply shuffle_tid_n_seq_point_correct.
    now apply seq_point_correct_cons in T.
  - apply swap_perm_trans with (t2:=(tid1, a1)::(tid2, a2)::t').
    apply swap_perm_swap; auto.
    apply swap_perm_skip.
    apply IHt0.
    apply spc_action.
    now do 2 apply seq_point_correct_cons in T.
    destruct a2; congruence.
  - apply swap_perm_skip.
    apply IHt0.
    now apply seq_point_correct_cons in T.
  - apply swap_permutation_refl.
Qed.

Eval compute in (swap_beta_n example_txn3 4).


Fixpoint tid_seq_point_distance tid t :=
  match t with
  | (tid', seq_point) :: t' =>
    if Nat.eq_dec tid tid' then 0 else S (tid_seq_point_distance tid t')
  | _ :: t' => S (tid_seq_point_distance tid t')
  | [] => 0
  end.

Fixpoint seq_point_distance_measure t :=
  match t with
  | (tid, validate_read_item _) :: t'
  | (tid, commit_txn) :: t'
  | (tid, complete_write_item _) :: t'
  | (tid, commit_done_txn) :: t' =>
    (S (tid_seq_point_distance tid t')) + seq_point_distance_measure t'
  | _ :: t' => seq_point_distance_measure t'
  | [] => 0
  end.
