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
(*
Inductive log : Type :=
|Read : address -> version -> log -> log
|Write : address -> value -> log -> log
|NilLog : log.

Function log_read_only (l:log) : Prop :=
  match l with
   | NilLog => True
   | Read _ _ s => log_read_only s
   | Write _ _ _ => False
  end.

Inductive operation :=
|  read: address -> variable -> operation
|  write: address -> value -> operation.

Definition transaction := list operation.

Inductive trans_state : Type :=
| TS: forall (s: store) (h: heap) (l: log), trans_state.

Inductive trans_step1 : relation trans_state :=
| TS_read: forall s h addr l var val lck ver,
	h addr = Some (val, lck, ver) ->
	lck = false -> 
	trans_step1 (TS s h l) (TS (NatMap.add var val s) h (Read addr ver l))
|TS_write: forall s h addr l val,
	trans_step1 (TS s h l) (TS s h (Write addr val l)).
*)
(*
1. What operations do we need to support? For example, non-transactional operations, write from a read, etc
2. What is the difference between the inductive style that we are using and the functional style?
   We followed your style in osview.
3. What is the next step?
4. How to model concurrency?

forall traces t, if t is sto_trace, then there exists a reorder trace t' where t' reorders t and t' is a sto-trace
and t' is a serial trace

Let's say each trace is each element belongs to a transaction
serial means all operations on a transaction grouped

Action:=
|start_txn: tid -> action
|read_item: tid -> addr -> action
|write_item: tid -> addr -> value -> action
|try_commit_txn: tid -> action
|lock_write_item: tid -> addr -> action
|validate_read_item: tid -> addr -> version -> action
|abort_txn: tid -> action
|complete_write_item: tid -> addr -> value -> action
|invalid_write_item: tid -> addr -> value -> action
|commit_txn: tid -> action
|obtain_global_tid (must call after all write items are locked)

global_tid order produces the same result, same memory and every read returns the same value

sto_trace may should be inductive type
should probably have a reorder operation
How do you define reorder? How do you define serial?
Do you want to use os_step trick of collecting explicit history?
** Reordering definition is important **
*)
Inductive action:=
|dummy: action
|start_txn: action
|read_item: version -> action
|write_item: value -> action
|try_commit_txn: action
|lock_write_item: action
|validate_read_item: Prop -> action
|abort_txn: action
(*|restart_txn: action*)
|complete_write_item: (*value -> action*)version -> action
(*|unlock_write_item: version -> action*)
(*|invalid_write_item: value -> action*)
|commit_txn: version -> action
|seq_point: action.
(*|obtain_global_tid: action.*)
(*sp later than last lock, but must before the first commit*)
Definition trace := list (tid * action).

(*
Returns all tid*action with tid tid in the trace.
*)
Definition trace_filter_tid tid tr : trace :=
    filter (fun pr => fst pr =? tid) tr.

(*
Returns all commit actions in the trace.
*)
Definition trace_filter_commit tr: trace :=
    filter (fun pr => match snd pr with
                      | commit_txn _ => true
                      | _ => false
                      end) tr.
(*
Returns all write actions in the trace.
*)
Definition trace_filter_write tr: trace :=
    filter (fun pr => match snd pr with
                      | write_item _ => true
                      | _ => false
                      end) tr.

(*
Returns all read actions in the trace.
*)
Definition trace_filter_read tr: trace :=
    filter (fun pr => match snd pr with
                      | read_item _ => true
                      | _ => false
                      end) tr.

(*
Returns all commit & complete_write actions in the trace for updating commit version
*)
Definition trace_filter_commit_complete tr: trace :=
    filter (fun pr => match snd pr with
                      | commit_txn _ => true
                      | complete_write_item _ => true
                      | _ => false
                      end) tr.

(*
Returns the last action of the transaction tid
Returns dummy if there is no transaction with id tid.
*)
Definition trace_tid_last tid t: action :=
    hd dummy (map snd (trace_filter_tid tid t)).

(*
Returns the version number of the last commit
If there is no commit in the trace, returns 0.
*)
Definition trace_commit_last t: version :=
  match hd dummy (map snd (trace_filter_commit t)) with
	| commit_txn n => n
	| _ => 0
  end.

(*
Returns the value of the last write
If there is no write in the trace, returns 0.
*)
Definition trace_write_last t: value :=
  match hd dummy (map snd (trace_filter_write t)) with
	| write_item n => n
	| _ => 0
  end.

(*
Returns the version number of the last commit/complete_write
If there is no commit in the trace, returns 0.
*)
Definition trace_commit_complete_last t: version :=
  match hd dummy (map snd (trace_filter_commit_complete t)) with
	| commit_txn n => n
  | complete_write_item n => n
	| _ => 0
  end.

(*
Returns all lock_write_item actions in the trace.
*)
Definition trace_filter_lock tr: trace :=
    filter (fun pr => match snd pr with
                      | lock_write_item => true
                      | _ => false
                      end) tr.

(*
All commit and abort have unlock_write_item.
If a transaction contains either of the actions, the transaction has unlock
*)
Definition trace_filter_unlock tr: trace :=
    filter (fun pr => match snd pr with
                      | commit_txn _ => true
                      | abort_txn => true
                      | _ => false
                      end) tr.

(*
Returns the length of a trace
*)
Function length (tr: trace) : nat := 
  match tr with 
  | [] => 0
  | _ :: tr' => S (length tr')
  end.

(*
Returns True if there exists no lock_write_item
Returns False if there exists locks
*)
Definition check_lock_or_unlock tr: Prop :=
  match 
    length (trace_filter_lock tr) <=? length (trace_filter_unlock tr)  
  with 
	| true => True
	| false => False
  end.


(*
Returns true if an action is not a write action
Returns false if an action is a write action.
*)
Definition action_no_write e : Prop :=
  match e with
  | write_item  _  => False
  | _ => True
  end.

(*
Returns true if an action is not a commit_txn action
Returns false if an action is a commit_txn action.
*)
Definition action_no_commit e : Prop :=
  match e with
  | commit_txn _ => False
  | _ => True
  end.

Definition action_no_seq_point e: Prop:=
    match e with
  | seq_point => False
  | _ => True
  end.
(*
Returns true if the transaction tid's trace has no writes
Returns false otherwise.
*)
Definition trace_no_writes tid t: Prop :=
  Forall action_no_write (map snd (trace_filter_tid tid t)).

(*
Returns true if the transaction tid's trace has no commits
Returns false otherwise.
*)
Definition trace_no_commits tid t: Prop :=
  Forall action_no_commit (map snd (trace_filter_tid tid t)).

Definition trace_no_seq_points tid t: Prop :=
  Forall action_no_seq_point (map snd (trace_filter_tid tid t)).
(*
Returns all read_item versions in a trace of a particular transaction.
*)
Function read_versions tr: list version :=
  match tr with
   | [] => []
   | (read_item v) :: tail =>  v :: read_versions tail
   | _ :: tail => read_versions tail
  end.

(*
Returns all read_item versions of tid in a trace tr.
*)
Definition read_versions_tid tid tr: list version :=
  read_versions (map snd (trace_filter_tid tid tr)).

(*
Returns True if reads are valid
Returns False otherwise
*)
Function check_version (vs : list version) (v : version) : Prop :=
  match vs with
  | [] => True
  | hd :: tail => if hd =? v then check_version tail v
                  else False
  end.

(*
Returns all start/read/write actions in the trace.
*)
Definition trace_filter_startreadwrite tid tr: trace :=
    filter (fun pr => (fst pr =? tid) &&
                      (match snd pr with
                      | read_item _ => true
                      | write_item _ => true
                      | start_txn => true
                      | _ => false
                      end)) tr.

(*
Returns all newtid with start/read/write actions in the trace.
*)
(*
Function trace_rollback (newtid: nat) (newver: version) (tr:trace): trace :=
    match tr with 
    | [] => []
    | (tid, read_item _) :: tr' 
      => [(newtid, read_item newver)] ++ trace_rollback newtid newver tr'
    | (tid, write_item val) :: tr'
      => [(newtid, write_item val)] ++ trace_rollback newtid newver tr'
    | (tid, start_txn) :: tr'
      => [(newtid, start_txn)] ++ trace_rollback newtid newver tr'
    | _ :: tr' => trace_rollback newtid newver tr'
  end.
*)

Inductive sto_trace : trace -> Prop :=

| empty_step : sto_trace []

| start_txn_step: forall t tid, 
    (*trace_tid_last tid t = dummy*)
    (* this tid doesn’t have start_txn*)
    trace_filter_tid tid t = []
    -> sto_trace t
    -> sto_trace ((tid, start_txn)::t)

| read_item_step: forall t tid val oldver,
    trace_tid_last tid t = start_txn (* start/read/write before read*)
		\/ trace_tid_last tid t = read_item oldver
    \/ trace_tid_last tid t = write_item val
    (*check locked or not*)
    -> check_lock_or_unlock t
    -> sto_trace t
    -> sto_trace ((tid, read_item (trace_commit_last t)) :: t)

| write_item_step: forall t tid oldval val ver, 
    trace_tid_last tid t = start_txn 
		\/ trace_tid_last tid t = read_item ver
    \/ trace_tid_last tid t = write_item oldval
    -> sto_trace t
    -> sto_trace ((tid, write_item val) :: t)

| try_commit_txn_step: forall t tid ver val,
			trace_tid_last tid t = read_item ver
			\/ trace_tid_last tid t = write_item val
			-> sto_trace t
			-> sto_trace ((tid, try_commit_txn)::t)

| lock_write_item_step: forall t tid,
			trace_tid_last tid t = try_commit_txn
			/\ ~ trace_no_writes tid t
      -> check_lock_or_unlock t
			-> sto_trace t
			-> sto_trace ((tid, lock_write_item) :: t)

| validate_read_item_step: forall t tid,
			(trace_tid_last tid t = try_commit_txn /\ trace_no_writes tid t ) (*read only*)
			\/ trace_tid_last tid t = lock_write_item (*lock write*)
			-> sto_trace t
			-> sto_trace ((tid, validate_read_item (check_version (read_versions_tid tid t)  (trace_commit_last t) ))::t)

(****************************************)
(*| abort_readonly_txn_step: forall t tid,
      trace_tid_last tid t = validate_read_item False (*invalid*)
      /\ trace_no_writes tid t
      -> sto_trace t
      -> sto_trace ((tid, abort_txn) :: t)

| abort_write_txn_step: forall t tid,
      trace_tid_last tid t = validate_read_item False (*invalid*)
      /\ ~ trace_no_writes tid t
      -> sto_trace t
      -> sto_trace ([(tid, abort_txn); (tid, unlock_write_item (trace_commit_last t))] ++ t)*)
(****************************************)

| abort_txn_step: forall t tid,
      trace_tid_last tid t = validate_read_item False 
      -> sto_trace t
      -> sto_trace ((tid, abort_txn) :: t) (*abort will contain unlock....*)
      
| complete_write_item_step: forall t tid,
			trace_tid_last tid t = validate_read_item True (*valid read*)
      /\ ~ trace_no_writes tid t
      -> sto_trace t
      -> sto_trace ((tid, complete_write_item (S (trace_commit_last t))) :: t)

(*| unlock_write_item_step: forall t tid ver,
      trace_tid_last tid t = complete_write_item ver
			/\ ~ trace_no_writes tid t (*locked*)
      -> sto_trace t
      -> sto_trace ((tid, unlock_write_item ver) :: t)*)

(****************************************)
(*| commit_readonly_txn_step: forall t tid,
      (trace_tid_last tid t = validate_read_item True /\ trace_no_writes tid t)(*read only*)
      -> sto_trace t
      -> sto_trace ((tid, commit_txn (trace_commit_last t)) :: t)

| commit_write_txn_step: forall t tid ver,
      trace_tid_last tid t = unlock_write_item ver(*unlock the write*)
      -> sto_trace t
      -> sto_trace ((tid, commit_txn ver) :: t).*)
(****************************************)

(*sequential point*)
| seq_point_step: forall t tid ver,
      (trace_tid_last tid t = validate_read_item True
        /\ trace_no_writes tid t)
      \/ (trace_tid_last tid t = complete_write_item ver
			  /\ ~ trace_no_writes tid t)
      (*-> trace_no_commits tid t*)
      -> trace_no_seq_points tid t
      -> sto_trace t
      -> sto_trace ((tid, seq_point) :: t)

| commit_txn_step: forall t tid,
      trace_tid_last tid t = seq_point
      -> sto_trace t
      -> sto_trace ((tid, commit_txn (trace_commit_complete_last t)) :: t).
Hint Constructors sto_trace.

(*we don't need to rollback, once a transaction aborts, it will 'disappear'. A new transaction will do its work.*)
(*| restart_txn_step: forall t tid newtid,
      trace_tid_last tid t = abort_txn (*we get abort and then restart*)
      -> sto_trace t
    (*our restart is to add back*)
      -> sto_trace ((trace_rollback newtid (trace_commit_last t) (trace_filter_startreadwrite tid t)) ++ t).*)

(*
Example sto_trace_example_rollback:  
sto_trace [(3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)].

assert (trace_commit_complete_last [(3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)] = 1).
{ unfold trace_commit_complete_last. simpl. auto. }
rewrite <- H. 
apply commit_txn_step; rewrite H. 
unfold trace_tid_last. simpl. auto.
clear H.

apply seq_point_step with (ver := 1).
unfold trace_tid_last. simpl. left. split. auto.
unfold trace_no_writes. simpl.
repeat apply Forall_cons; simpl; auto.
unfold trace_no_commits. simpl.
repeat apply Forall_cons; simpl; auto.

assert ((check_version (read_versions_tid 3 ([(3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) (trace_commit_last ([(3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) = True)).
  {unfold check_version. simpl. auto. } 
  rewrite <- H.

apply validate_read_item_step.
unfold trace_tid_last. simpl. left. split. auto.
unfold trace_no_writes.
repeat apply Forall_cons; simpl; auto. rewrite H.
clear H.

apply try_commit_txn_step with (ver:= 1) (val:= 0).
unfold trace_tid_last. simpl. left. auto.

(*assert (trace_rollback 3 (trace_commit_last [(1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, unlock_write_item 1); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)]) (trace_filter_startreadwrite 1 [(1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, unlock_write_item 1); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)]) = [(3, read_item 1); (3, start_txn)]).
unfold trace_rollback. simpl.
unfold trace_commit_last. simpl. auto.

assert ([(3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, unlock_write_item 1); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)] = [(3, read_item 1); (3, start_txn)] ++ [(1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, unlock_write_item 1); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)]). auto.
rewrite H0. rewrite <- H.
apply restart_txn_step. unfold trace_tid_last. simpl. auto. clear H H0.
*)

assert (trace_commit_last [(3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)] = 1).
{unfold trace_commit_last; simpl. auto. }
rewrite <- H.
apply read_item_step with (val:=0) (oldver:=0); rewrite H.
unfold trace_tid_last. simpl. left. auto.
unfold check_lock_or_unlock. simpl. auto. clear H.
 
apply start_txn_step. 
unfold trace_tid_last. simpl. auto.

apply abort_txn_step.
unfold trace_tid_last. simpl. auto.

assert ((check_version (read_versions_tid 1 ([(1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) (trace_commit_last ([(1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) = False)).
unfold check_version. simpl. auto.
rewrite <- H. 
apply validate_read_item_step. 
unfold trace_tid_last. simpl. left. split. auto.
unfold trace_no_writes. simpl.
repeat apply Forall_cons; simpl; auto.
clear H.

apply try_commit_txn_step with (ver:= 0) (val:= 4).
unfold trace_tid_last. simpl. auto.


assert (trace_commit_complete_last [ (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)] = 1).
{ unfold trace_commit_complete_last. simpl. auto. }
rewrite <- H.
apply commit_txn_step; rewrite H.
unfold trace_tid_last. simpl. auto.

apply seq_point_step with (ver:=1). right.
unfold trace_tid_last. simpl. split. auto.
unfold trace_no_writes. simpl.
intuition. 
inversion H0. inversion H4. inversion H8. inversion H12. inversion H16.
simpl in H19. auto. 
unfold trace_no_commits. simpl.
repeat apply Forall_cons; simpl; auto.
(*
apply unlock_write_item_step.
unfold trace_tid_last. simpl. split. auto.
unfold trace_no_writes. simpl.
intuition. 
inversion H. inversion H3. inversion H7. inversion H11. inversion H15.
simpl in *. auto.
*)
clear H.
assert (trace_commit_last ([(2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)]) = 0).
{ unfold trace_commit_last. simpl. auto. }
assert (1 = S (trace_commit_last [(2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])).
{ rewrite H. auto. }
rewrite H0.

apply complete_write_item_step; rewrite <-H0.
unfold trace_tid_last. simpl. split. auto.
unfold trace_no_writes. simpl.
intuition.
inversion H1. inversion H5. inversion H9. inversion H13.
simpl in *. auto.
clear H H0.
assert ((check_version (read_versions_tid 2 ([(2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) (trace_commit_last ([(2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) = True)).
  {unfold check_version. simpl. auto. }
  rewrite <- H.

apply validate_read_item_step. 
unfold trace_tid_last. simpl. right. auto. clear H.

apply lock_write_item_step. split.
unfold trace_tid_last. simpl. auto.
unfold trace_no_writes. simpl.
intuition.
inversion H. inversion H3. simpl in *. auto.
unfold check_lock_or_unlock. simpl. auto.

apply try_commit_txn_step with (ver := 0) (val:= 4).
unfold trace_tid_last. simpl. auto.

apply write_item_step with (ver:=0) (oldval:=0).
unfold trace_tid_last. simpl. right. left. auto.

assert (trace_commit_last [(2, read_item 0); (2, start_txn); (1, start_txn)] = 0).
{unfold trace_commit_last; simpl. auto. }
rewrite <- H.
apply read_item_step with (val:=0) (oldver:=0); rewrite H. clear H.
unfold trace_tid_last. simpl. left. auto.
unfold check_lock_or_unlock. simpl. auto.

assert (trace_commit_last [(2, start_txn); (1, start_txn)] = 0).
{unfold trace_commit_last; simpl. auto. }
rewrite <- H0.
apply read_item_step with (val:=0) (oldver:=0); rewrite H0. clear H H0.
unfold trace_tid_last. simpl. left. auto.
unfold check_lock_or_unlock. simpl. auto.

apply start_txn_step. unfold trace_tid_last. auto.
apply start_txn_step. unfold trace_tid_last. auto.

apply empty_step.

Example sto_trace_example_commit:  
sto_trace [(2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, commit_txn 0); (1, seq_point); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)].

assert (trace_commit_complete_last [(2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, commit_txn 0); (1, seq_point); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)] = 1).
{ unfold trace_commit_complete_last. simpl. auto. }
rewrite <- H. 
apply commit_txn_step.
unfold trace_tid_last; rewrite H. simpl. auto. rewrite H. clear H.

apply seq_point_step with (ver:= 1). 
unfold trace_tid_last. simpl. right. split. auto.
unfold trace_no_writes. simpl.
intuition. 
inversion H. inversion H3. inversion H7. inversion H11. inversion H15.
simpl in H18. auto.
unfold trace_no_commits. simpl.
repeat apply Forall_cons; simpl; auto.

assert (trace_commit_last ([(2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, commit_txn 0); (1, seq_point);  (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)]) = 0).
{ unfold trace_commit_last. simpl. auto. }
assert (1 = S (trace_commit_last [(2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, commit_txn 0); (1, seq_point);  (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0);(2, read_item 0); (2, start_txn); (1, start_txn)])).
{ rewrite H. auto. }
rewrite H0.

apply complete_write_item_step; rewrite <-H0.
unfold trace_tid_last. simpl. split. auto.
unfold trace_no_writes. simpl.
intuition.
inversion H1. inversion H5. inversion H9. inversion H13.
simpl in *. auto.
clear H H0.
assert ((check_version (read_versions_tid 2 ([(2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, commit_txn 0); (1, seq_point); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) (trace_commit_last ([(2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, commit_txn 0); (1, seq_point); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) = True)).
  {unfold check_version. simpl. auto. }
  rewrite <- H.

apply validate_read_item_step; rewrite H. 
unfold trace_tid_last. simpl. right. auto. clear H.

apply lock_write_item_step. split.
unfold trace_tid_last. simpl. auto.
unfold trace_no_writes. simpl.
intuition.
inversion H. inversion H3. simpl in *. auto.
unfold check_lock_or_unlock. simpl. auto.

apply try_commit_txn_step with (ver := 0) (val:= 4).
unfold trace_tid_last. simpl. auto.

apply write_item_step with (ver:=0) (oldval:=0).
unfold trace_tid_last. simpl. right. left. auto.

assert (trace_commit_complete_last [ (1, seq_point); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)] = 0).
{ unfold trace_commit_complete_last. simpl. auto. }
rewrite <- H. 
apply commit_txn_step; rewrite H.
unfold trace_tid_last. simpl. auto.

apply seq_point_step with (ver:= 0).
unfold trace_tid_last. simpl. left. split. auto.
clear H.
unfold trace_no_writes. simpl.
repeat apply Forall_cons; simpl; auto. clear H.
unfold trace_no_commits. simpl.
repeat apply Forall_cons; simpl; auto. clear H.

assert ((check_version (read_versions_tid 1 ([(1, try_commit_txn); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) (trace_commit_last ([(1, try_commit_txn); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)])) = True)).
  {unfold check_version. simpl. auto. } 
  rewrite <- H.

apply validate_read_item_step.
unfold trace_tid_last. simpl. left. split. auto.
unfold trace_no_writes.
repeat apply Forall_cons; simpl; auto.
clear H.

apply try_commit_txn_step with (ver:= 0) (val:= 0).
unfold trace_tid_last. simpl. left. auto.

assert (trace_commit_last [(2, read_item 0); (2, start_txn); (1, start_txn)] = 0).
{unfold trace_commit_last; simpl. auto. }
rewrite <- H.

apply read_item_step with (val:=0) (oldver:=0); rewrite H. clear H.
unfold trace_tid_last. simpl. left. auto.
unfold check_lock_or_unlock. simpl. auto.

assert (trace_commit_last [(2, start_txn); (1, start_txn)] = 0).
{unfold trace_commit_last; simpl. auto. }
rewrite <- H0.

apply read_item_step with (val:=0) (oldver:=0); rewrite H0. clear H H0.
unfold trace_tid_last. simpl. left. auto.
unfold check_lock_or_unlock. simpl. auto.

apply start_txn_step. unfold trace_tid_last. auto.
apply start_txn_step. unfold trace_tid_last. auto.

apply empty_step.
*)
Definition example_txn:=
[(2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (2, read_item 0); (2, start_txn); (1, commit_txn 0); (1, seq_point); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (1, start_txn)].

Definition example_txn2:=
[(3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)].

Lemma sto_trace_app tid action t:
  sto_trace ((tid, action) :: t) -> sto_trace t.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma sto_trace_app2 t1 t2:
  sto_trace (t1 ++ t2) -> sto_trace t2.
Proof.
  intros.
  induction t1. rewrite app_nil_l in H. auto.
  simpl in *. destruct a. 
  apply sto_trace_app with (tid0 := t) (action0:= a) in H.
  apply IHt1 in H. auto.
Qed.
(* some error with this lemma
Lemma sto_trace_app2 tid tid0 action action0 t:
  tid <> tid0 -> sto_trace ((tid, action) :: (tid0, action0) :: t) -> sto_trace ((tid, action) :: t).
Proof.
  intros.
  inversion H0; subst.
  apply sto_trace_app in H5. unfold trace_tid_last in H3; simpl in H3.
  apply not_eq_sym in H. apply Nat.eqb_neq in H; rewrite H in H3.
  apply start_txn_step with (tid := tid) in H5; [ auto | unfold trace_tid_last; auto ].
  apply sto_trace_app in H6. unfold trace_tid_last in H4; simpl in H4.
  apply not_eq_sym in H. apply Nat.eqb_neq in H; rewrite H in H4.
  unfold check_lock_or_unlock in H5. unfold trace_filter_lock in H5.
  unfold trace_filter_unlock in H5.
  apply read_item_step with (tid := tid) (val := val) (oldver := oldver) in H6; [ auto | unfold trace_tid_last; auto | auto].
Qed.
*)

(*
Returns the serialized sequence of transactions in the STO trace based on seq_point of each transaction
The first element (tid) of the sequence is the first transaction that completes in the serial trace
Note that STO-trace is constructed in a reverse order: the first (tid * action) pair is the last operation in the trace
*)

Function seq_list (sto_trace: trace): list nat:=
  match sto_trace with
  | [] => []
  | (tid, seq_point) :: tail => tid :: seq_list tail
  | (tid, dummy) :: tail => seq_list tail
  | (tid, start_txn) :: tail => seq_list tail
  | (tid, read_item n) :: tail => seq_list tail
  | (tid, write_item n) :: tail => seq_list tail
  | (tid, try_commit_txn) :: tail => seq_list tail
  | (tid, lock_write_item) :: tail => seq_list tail
  | (tid, validate_read_item b) :: tail => seq_list tail
  | (tid, abort_txn) :: tail => seq_list tail
  | (tid, complete_write_item n) :: tail => seq_list tail
  | (tid, commit_txn n) :: tail => seq_list tail
  end.

Eval compute in seq_list example_txn.

Eval compute in seq_list example_txn2.

Lemma seq_list_not_seqpoint tid action t:
  sto_trace ((tid, action) :: t) ->
  action <> seq_point -> 
  ~ In tid (seq_list ((tid, action) :: t)) 
  -> ~ In tid (seq_list t).
Proof.
  intros; destruct action; simpl in *; auto.
Qed.

Lemma seq_list_not_seqpoint2 tid action t:
  sto_trace ((tid, action) :: t) ->
  ~ In tid (seq_list ((tid, action) :: t)) 
  -> ~ In tid (seq_list t).
Proof.
  intros; destruct action; simpl in *; auto.
Qed.

Lemma seq_list_seqpoint tid action t:
  sto_trace ((tid, action) :: t) ->
  action = seq_point -> 
  In tid (seq_list ((tid, action) :: t)).
Proof.
  intros; subst; simpl.
  left. auto.
Qed.

Lemma trace_seqlist_seqpoint t tid:
  In (tid, seq_point) t
  -> In tid (seq_list t).
Proof.
  intros.
  functional induction seq_list t.
  inversion H.
  destruct (Nat.eq_dec tid tid0); subst; simpl.
  left. auto.
  right. apply IHl. apply in_inv in H. destruct H.
  inversion H. apply Nat.eq_sym in H1. contradiction. auto.
  all: destruct (Nat.eq_dec tid tid0); subst; apply IHl; apply in_inv in H; destruct H; try inversion H; auto.
Qed.

Lemma trace_seqlist_seqpoint_rev t tid:
  In tid (seq_list t)
  -> In (tid, seq_point) t.
Proof.
  intros.
  functional induction seq_list t.
  inversion H.
  destruct (Nat.eq_dec tid tid0); subst; simpl; simpl in H. left. auto.
  destruct H. apply eq_sym in H. congruence. apply IHl in H. right. auto.
  all: destruct (Nat.eq_dec tid tid0); subst; apply in_cons; auto.
Qed.

Lemma filter_app (f: nat * action -> bool) l1 l2:
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1.
  - simpl. auto.
  - Search (filter).
    simpl. remember (f a) as X. destruct X. 
    simpl. rewrite IHl1. auto. auto.
Qed.
Lemma trace_filter_tid_app tid tr1 tr2:
  trace_filter_tid tid (tr1 ++ tr2) =
  trace_filter_tid tid tr1 ++ trace_filter_tid tid tr2.
Proof.
  unfold trace_filter_tid. 
  apply filter_app.
Qed.
Lemma Forall_app (P: action -> Prop) l1 l2:
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  split.
  - intros. split;
    rewrite Forall_forall in *. 
    intros. Search (In _ ( _ ++ _ )).
    assert (In x l1 \/ In x l2 -> In x (l1 ++ l2)). apply in_or_app.
    assert (In x l1 \/ In x l2). left. auto. 
    apply H1 in H2. auto.
    intros.
    assert (In x l1 \/ In x l2 -> In x (l1 ++ l2)). apply in_or_app.
    assert (In x l1 \/ In x l2). right. auto. 
    apply H1 in H2. auto.
  - intros. destruct_pairs.
    rewrite Forall_forall in *. Search (In _ ( _ ++ _ )).
    intros.
    apply in_app_or in H1.
    (* firstorder. solved here*)
    destruct H1.
    apply H in H1. auto. apply H0 in H1. auto.
Qed.

Lemma seq_list_no_two_seqpoint t tid:
  sto_trace ((tid, seq_point) :: t)
  -> ~ In (tid, seq_point) t.
Proof.
  intros.
  assert (sto_trace t). { apply sto_trace_app with (tid0 := tid) (action0 := seq_point). auto. }
  inversion H.
  intuition.
  unfold trace_no_seq_points in H4.
  apply in_split in H6.
  destruct H6. destruct H6.
  rewrite H6 in H4. simpl in H4.
  rewrite trace_filter_tid_app in H4.
  simpl in H4.
  rewrite <-beq_nat_refl in H4. 
  rewrite map_app in H4.
  rewrite Forall_app in H4.
  destruct H4. simpl in H7. 
  apply Forall_inv in H7. simpl in H7. auto.
  unfold trace_no_seq_points in H4.
  apply in_split in H6.
  destruct H6. destruct H6.
  rewrite H6 in H4. simpl in H4.
  rewrite trace_filter_tid_app in H4.
  simpl in H4.
  rewrite <-beq_nat_refl in H4. 
  rewrite map_app in H4.
  rewrite Forall_app in H4.
  destruct H4. simpl in H7. 
  apply Forall_inv in H7. simpl in H7. auto.
Qed.

Lemma seq_list_no_two_seqpoint2 t1 t2 tid:
  sto_trace (t1 ++ (tid, seq_point) :: t2)
  -> ~ In (tid, seq_point) t1.
Proof.
  intros.
  intuition.
  apply in_split in H0. destruct H0. destruct H0.
  rewrite H0 in H.
  rewrite <- app_assoc in H.
  apply sto_trace_app2 in H.
  inversion H; subst.
  unfold trace_no_seq_points in H4.
  rewrite trace_filter_tid_app in H4.
  rewrite map_app in H4. rewrite Forall_app in H4.
  destruct H4. simpl in H1. rewrite <- beq_nat_refl in H1.
  simpl in H1. apply Forall_inv in H1. simpl in H1. auto.
Qed.

Lemma seq_point_after t1 t2 tid action:
  sto_trace ((tid, action) :: t1 ++ (tid, seq_point) :: t2)
  -> action = commit_txn (trace_commit_complete_last (t1 ++ (tid, seq_point) :: t2)).
Proof.
  intros.
  induction t1.
  simpl in H.
  inversion H; subst.
  simpl in H2. rewrite <- beq_nat_refl in H2. inversion H2.
  unfold trace_tid_last in H3. simpl in H3. rewrite <- beq_nat_refl in H3. repeat destruct or H3; inversion H3.
  unfold trace_tid_last in H2. simpl in H2. rewrite <- beq_nat_refl in H2. repeat destruct or H2; inversion H2.
  unfold trace_tid_last in H2. simpl in H2. rewrite <- beq_nat_refl in H2. repeat destruct or H2; inversion H2.
  unfold trace_tid_last in H3. simpl in H3. rewrite <- beq_nat_refl in H3. destruct H3. simpl in H0. inversion H0.
  unfold trace_tid_last in H2. simpl in H2. rewrite <- beq_nat_refl in H2. destruct H2. destruct H0. simpl in H0. inversion H0. simpl in H0. inversion H0.
  unfold trace_tid_last in H2. simpl in H2. rewrite <- beq_nat_refl in H2. inversion H2.
  unfold trace_tid_last in H2. simpl in H2. rewrite <- beq_nat_refl in H2. destruct H2. inversion H0.
  unfold trace_tid_last in H3. simpl in H3. rewrite <- beq_nat_refl in H3. repeat destruct or H3. destruct H3. inversion H0. destruct H3. inversion H0.
  auto.
  destruct a. 
  admit.
Admitted.

(* useless lemma
Lemma seq_list_last_tid_dummy tid t:
  sto_trace t ->
  In tid (seq_list t) ->
  trace_tid_last tid t <> dummy.
Proof.
  intros ST; induction ST; intros.
  all: cbn in *.
  contradiction.
  all: unfold trace_tid_last; simpl.
  all: destruct (Nat.eq_dec tid0 tid);
    [ subst; rewrite <- beq_nat_refl; cbn; discriminate | ].
  all: apply Nat.eqb_neq in n; rewrite n.
  all: try apply IHST in H0; auto.
  apply in_app_or in H1.
  destruct H1. apply IHST in H1; auto.
  simpl in H1. destruct H1. apply Nat.eqb_neq in n. contradiction. inversion H1.
Qed.
*)
Lemma seq_list_last_tid_start_txn tid t:
  sto_trace t ->
  In tid (seq_list t) ->
  trace_tid_last tid t <> start_txn.
Proof.
  intros ST; induction ST; intros.
  all: cbn in *.
  contradiction.
  all: unfold trace_tid_last; simpl; destruct (Nat.eq_dec tid0 tid); [subst |].
  apply trace_seqlist_seqpoint_rev in H0.
  apply in_split in H0. destruct H0. destruct H0.
  rewrite H0 in H. rewrite trace_filter_tid_app in H. simpl in H.
  rewrite <- beq_nat_refl in H. apply app_eq_nil in H. destruct H.
  inversion H1.
  apply IHST in H0. unfold trace_tid_last in H0.
  apply Nat.eqb_neq in n; rewrite n. auto.

  all: try rewrite <- beq_nat_refl; simpl; try congruence.
  all: apply Nat.eqb_neq in n; rewrite n; try apply IHST in H1; auto.
  
  apply Nat.eqb_neq in n. destruct H1. congruence.
  apply IHST in H1; auto.
Qed.
(*
Lemma seq_list_last_tid_read_item tid t:
  sto_trace t ->
  In tid (seq_list t) ->
  exists ver, trace_tid_last tid t <> read_item ver.
Proof.
  intros ST; induction ST; intros.
  all: cbn in *.
  contradiction.
  all: unfold trace_tid_last; simpl; destruct (Nat.eq_dec tid0 tid); [subst |].
  apply trace_seqlist_seqpoint_rev in H0.
  apply in_split in H0. destruct H0. destruct H0.
  rewrite H0 in H. rewrite trace_filter_tid_app in H. simpl in H.
  rewrite <- beq_nat_refl in H. apply app_eq_nil in H. destruct H.
  inversion H1.
  apply IHST in H0. unfold trace_tid_last in H0.
  apply Nat.eqb_neq in n; rewrite n. auto.

  all: try rewrite <- beq_nat_refl; simpl; try congruence.
  all: apply Nat.eqb_neq in n; rewrite n; try apply IHST in H1; auto.
  
  apply Nat.eqb_neq in n. apply in_app_or in H1. destruct H1.
  apply IHST in H1; auto.
  simpl in H1. destruct H1. congruence. contradiction.
Qed.*)

Ltac remove_unrelevant_last_txn :=
  repeat match goal with
  | [H: context[trace_tid_last ?tid ((?tid0, _) :: ?t) = _] |-_] =>
      unfold trace_tid_last in H; inversion H;
      destruct (Nat.eq_dec tid tid0); subst
  | [H: context[hd _
       (map snd
          (if ?tid0 =? ?tid0
           then (?tid0, ?x) :: trace_filter_tid ?tid0 ?t
           else trace_filter_tid ?tid0 ?t)) = ?y] |-_] =>
      rewrite <- beq_nat_refl in H; simpl in H; inversion H
  | [H: context[?tid <> ?tid0] |-_] =>
      apply not_eq_sym in H; apply Nat.eqb_neq in H
end.

Lemma seq_list_commit tid t:
  sto_trace t -> 
  trace_tid_last tid t = seq_point
  -> In tid (seq_list t).
Proof.
  intros.
  induction H; simpl; try discriminate.
  1, 3, 4, 6-8, 10: remove_unrelevant_last_txn; rewrite n in H3; apply IHsto_trace in H3; auto.
  1, 2: remove_unrelevant_last_txn; rewrite n in H4; apply IHsto_trace in H4; auto.
  remove_unrelevant_last_txn.
  left. auto.
  rewrite n in H4. 
  apply IHsto_trace in H4. 
  right. auto.
Qed.


Lemma seq_point_before_commit (t:trace) (tid: tid) n:
  sto_trace ((tid, commit_txn n) :: t) ->
  In (tid, seq_point) t.
Proof.
  intros.
  inversion H.
  apply seq_list_commit in H2.
  apply trace_seqlist_seqpoint_rev in H2.
  auto. auto.
Qed.

Lemma seq_point_before_commit2 t tid action:
  sto_trace ((tid, action) :: t) ->
  In (tid, seq_point) t ->
  action = commit_txn (trace_commit_complete_last t).
Proof.
  intros.
  apply in_split in H0. destruct H0. destruct H0. rewrite H0 in H.
  apply seq_point_after in H.
  subst. auto.
Qed. 

(*
Lemma seq_point_one_commit t:
  sto_trace ((tid, action) :: t1 ++ (tid, seq_point) :: t2) 
  -> exists n, action = commit_txn n /\ *)
Lemma seq_list_action tid action t:
  sto_trace ((tid, action) :: t) -> 
  action = seq_point \/ action = commit_txn (trace_commit_complete_last t)
  <-> In tid (seq_list ((tid, action) :: t)).
Proof.
  split.
  intros. destruct H0.
  apply seq_list_seqpoint; auto.
  subst. inversion H; subst.
  simpl. apply seq_list_commit; auto.
  
  intros.
  apply trace_seqlist_seqpoint_rev in H0.
  apply in_inv in H0.
  destruct H0.
  inversion H0. left. auto.
  right.
  apply seq_point_before_commit2 with (action0 := action) in H0.
  destruct H0. auto. auto.
Qed.


Lemma seq_list_action_neg tid action t:
  sto_trace ((tid, action) :: t) -> 
  action <> seq_point /\ action <> commit_txn (trace_commit_complete_last t)
  <-> ~ In tid (seq_list ((tid, action) :: t)).
Proof.
  intros. split. 
  intros. 
  intuition.
  apply seq_list_action in H .
  destruct H. apply H0 in H1. destruct H1; auto.
  intros.
  intuition.
  apply seq_list_action in H .
  destruct H.
  assert (action = seq_point \/ action = commit_txn (trace_commit_complete_last t)). { left. auto. }
  apply H in H3. auto.
  apply seq_list_action in H .
  destruct H.
  assert (action = seq_point \/ action = commit_txn (trace_commit_complete_last t)). { right. auto. }
  apply H in H3. auto.
Qed.

Lemma seqlist_filter t t' tid:
  sto_trace t
  -> ~ In (tid, seq_point) t
  -> seq_list (trace_filter_tid tid t ++ t') = seq_list t'.
Proof.
  intros.
  induction H; simpl; auto.
  all: destruct (Nat.eq_dec tid0 tid); subst.
  all: simpl in H0; apply not_or_and in H0; destruct H0; try apply IHsto_trace in H2.
  all: try rewrite <- beq_nat_refl; simpl; auto.
  all: try rewrite <- Nat.eqb_neq in n; try rewrite n; auto.
  intuition.
Qed.

Lemma seq_list_split_no_seqpoint t1 t2:
  seq_list (t1 ++ t2) = seq_list t1 ++ seq_list t2.
Proof.
  intros.
  induction t1.
  simpl. auto.
  simpl in *. destruct a. destruct a.
  all: simpl in *; auto.
  rewrite IHt1. auto.
Qed.

Lemma seq_list_split_with_seqpoint t1 tid t2:
  seq_list (t1 ++ (tid, seq_point) :: t2) = seq_list t1 ++ tid :: (seq_list t2).
Proof.
  intros.
  rewrite seq_list_split_no_seqpoint.
  simpl in *. auto.
Qed.
(*
This function creates a serialized trace.
Just like STO-trace, the order is reversed: that is, the first (tid*action) pair in the serial trace
constructed by this function is the last operation performed in this trace
*)

Function create_serialized_trace (sto_trace: trace) (seqls : list nat): trace:=
  match seqls with
  | [] => []
  | head :: tail 
    => trace_filter_tid head sto_trace ++ create_serialized_trace sto_trace tail
  end.

(*
Function create_serialized_trace (sto_trace: trace) (sto_trace_copy: trace): trace:=
  match sto_trace with
  | [] => []
  | (tid, seq_point) :: tail
    => trace_filter_tid tid sto_trace_copy ++ create_serialized_trace tail sto_trace_copy
  | _ :: tail => create_serialized_trace tail sto_trace_copy
  end.

Eval compute in create_serialized_trace example_txn example_txn.

Eval compute in create_serialized_trace example_txn2 example_txn2.

Lemma serial_action_remove tid action t:
  sto_trace ((tid, action) :: t) ->
  ~ In (tid, seq_point) t -> 
  create_serialized_trace t ((tid, action) :: t) = create_serialized_trace t t.
Proof.
  intros.
  apply sto_trace_app in H.
  induction H. 
  simpl. auto.
  simpl.
Admitted.

*)

Lemma serial_action_remove tid action t:
  sto_trace ((tid, action) :: t) ->
  ~ In tid (seq_list t) -> 
  create_serialized_trace ((tid, action) :: t) (seq_list t)= create_serialized_trace t (seq_list t).
Proof.
  intros.
  induction (seq_list t).
  simpl. auto.
  simpl.
  simpl in H0.
  assert (a <> tid /\ ~ In tid l). { intuition. }
  destruct H1.
  apply not_eq_sym in H1. rewrite <- Nat.eqb_neq in H1. rewrite H1.
  apply IHl in H2. rewrite H2. auto.
Qed.

Lemma serial_action_helper tid action t:
  sto_trace ((tid, action) :: t) ->
  action <> seq_point /\ action <> commit_txn (trace_commit_complete_last t)
  -> create_serialized_trace ((tid, action) :: t) (seq_list ((tid, action) :: t)) = 
     create_serialized_trace t (seq_list t).
Proof.
  intros.
  assert (sto_trace ((tid, action) :: t)). { auto. }
  assert (sto_trace ((tid, action) :: t)). { auto. }
  inversion H; subst.
  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := start_txn) in H1; [auto | auto].

  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := read_item (trace_commit_last t)) in H1; [auto | auto].

  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := write_item val) in H1; [auto | auto]. 

  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := try_commit_txn) in H1; [auto | auto].
   
  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := lock_write_item) in H1; [auto | auto].

  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := validate_read_item
     (check_version (read_versions_tid tid t) (trace_commit_last t))) in H1; [auto | auto].

  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := abort_txn) in H1; [auto | auto].

  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := complete_write_item (S (trace_commit_last t))) in H1; [auto | auto].

  apply seq_list_action_neg in H. destruct H. apply H in H0.
  simpl in H0. 
  assert (~ In tid (seq_list t) /\ ~ In tid [tid]). { intuition. }
  simpl in H4. destruct H4. intuition H5.
  
  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := commit_txn (trace_commit_complete_last t)) in H1; [auto | auto].
Qed.

Lemma serial_action_helper2 tid t:
  sto_trace ((tid, seq_point)::t)
  -> create_serialized_trace ((tid, seq_point)::t) (seq_list ((tid, seq_point)::t)) = trace_filter_tid tid ((tid, seq_point)::t) ++ create_serialized_trace t (seq_list t).
Proof.
  intros. simpl.
  rewrite <- beq_nat_refl. 
  assert (sto_trace ((tid, seq_point) :: t)). { auto. }
  apply seq_list_no_two_seqpoint in H.
  assert (~ In (tid, seq_point) t -> ~ In tid (seq_list t)). { intuition. apply trace_seqlist_seqpoint_rev in H2. auto. }
  apply H1 in H.
  apply serial_action_remove with (action0:= seq_point) in H.
  rewrite H. auto. auto.
Qed.

Lemma serial_action_seq_list tid action t:
  sto_trace ((tid, action) :: t) -> 
  ~ In tid (seq_list ((tid, action) :: t))
  -> create_serialized_trace ((tid, action) :: t) (seq_list ((tid, action) :: t)) = create_serialized_trace t (seq_list t).
Proof.
  intros.
  assert (sto_trace ((tid, action):: t)). { auto. }
  assert (sto_trace ((tid, action):: t)). { auto. }
  assert (~ In tid (seq_list t)). { apply seq_list_not_seqpoint2 with (action0:= action); auto. }
  apply seq_list_action_neg in H. destruct H. apply H4 in H0.
  destruct action; simpl; try apply serial_action_helper; auto.
  destruct H0. congruence.
Qed.

(*
This lemma proves that the seq_point of each transaction in a STO-trace determines its serialized order in the serial trace
*)


Lemma serial_action_split tid t t1 t2:
  sto_trace t
  -> t = t1 ++ (tid, seq_point) :: t2
  -> create_serialized_trace t (seq_list t) = 
  create_serialized_trace t (seq_list t1) ++ trace_filter_tid tid ((t1 ++ (tid, seq_point) :: t2)) ++ create_serialized_trace t (seq_list t2).
Proof.
  intros. rewrite H0 in *. rewrite seq_list_split_with_seqpoint.
  clear H H0.
  induction (seq_list t1).
  simpl in *. auto.
  simpl. rewrite IHl.
  apply app_assoc.
Qed.

Lemma serial_action_before_commit tid t1 t2 t:
  sto_trace t
  -> t = t1 ++ (tid, seq_point) :: t2
  -> create_serialized_trace ((tid, commit_txn (trace_commit_complete_last t)) :: t) (seq_list ((tid, commit_txn (trace_commit_complete_last t)) :: t)) = 
  create_serialized_trace t (seq_list t1) ++ (tid, commit_txn (trace_commit_complete_last t)) :: trace_filter_tid tid t ++ create_serialized_trace t (seq_list t2).
Proof.
  intros.
  assert (~ In tid (seq_list t2)).
  { rewrite H0 in H. apply sto_trace_app2 in H. apply seq_list_not_seqpoint in H. auto.
  
(*


  rewrite H0 in *. apply seq_list_split_with_seqpoint in H.
  simpl. rewrite H in *. clear H H0.
  induction (seq_list t1).
  simpl in *. rewrite <- beq_nat_refl. auto.*)
Admitted.

Lemma seq_list_equal trace:
  sto_trace trace -> 
  seq_list (create_serialized_trace trace (seq_list trace)) = seq_list trace.
Proof.
  intros. simpl.
  induction H; simpl.
  auto.
  apply start_txn_step with (tid0 := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1. auto.
  apply read_item_step with (tid := tid0) (val:= val) (oldver:= oldver) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H2. auto. auto.
  apply write_item_step with (tid := tid0) (ver:= ver) (oldval:= oldval) (val := val) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1. auto.
  apply try_commit_txn_step with (tid := tid0) (ver:= ver) (val:= val) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1. auto.
  apply lock_write_item_step with (tid := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H2. auto. auto.
  apply validate_read_item_step with (tid := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1. auto.
  apply abort_txn_step with (tid := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1. auto. 
  apply complete_write_item_step with (tid := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1. auto.
  
  rewrite <- beq_nat_refl. simpl.
  apply seq_point_step with (tid:= tid0) (ver := ver) in H1.
  assert (sto_trace ((tid0, seq_point) :: t)). { auto. }
  apply seq_list_no_two_seqpoint in H1.
  assert (~ In (tid0, seq_point) t -> ~ In tid0 (seq_list t)). { intuition; apply trace_seqlist_seqpoint_rev in H4; apply H3 in H4; auto. }
  apply H3 in H1.
  apply serial_action_remove with (action0 := seq_point) in H1.
  rewrite <- H1 in IHsto_trace.
  assert (seq_list (trace_filter_tid tid0 t ++ create_serialized_trace ((tid0, seq_point) :: t) (seq_list t)) = seq_list (create_serialized_trace ((tid0, seq_point) :: t) (seq_list t))). { apply seqlist_filter. assert (sto_trace ((tid0, seq_point) :: t)). { auto. } apply sto_trace_app in H2. auto. apply seq_list_no_two_seqpoint in H2. auto. }
  rewrite H4.
  remember  (seq_list (create_serialized_trace ((tid0, seq_point) :: t) (seq_list t))) as too_long. rewrite <- IHsto_trace. rewrite Heqtoo_long. auto.
  auto. auto. auto. 
  
  apply commit_txn_step with (tid:= tid0) in H0.
  assert (sto_trace ((tid0, commit_txn (trace_commit_complete_last t)) :: t)). { auto. }
  apply seq_point_before_commit in H0.
  apply in_split in H0. destruct H0. destruct H0.
  assert (sto_trace t). { apply sto_trace_app in H1. auto. }
  assert (t = x ++ (tid0, seq_point) :: x0). { auto. }
  assert (t = x ++ (tid0, seq_point) :: x0). { auto. }
  apply serial_action_before_commit in H0. simpl in H0.
  unfold tid in H0. rewrite H0.
  rewrite seq_list_split_no_seqpoint. simpl.
  apply serial_action_split in H3. rewrite H3 in IHsto_trace. 
  rewrite <- IHsto_trace. rewrite H4.
  rewrite <- seq_list_split_no_seqpoint. auto. auto. auto. auto. 
Qed.

Lemma serial_action_add tid t:
  sto_trace t
  -> sto_trace (create_serialized_trace t (seq_list t))
  -> ~ In tid (seq_list t)
  -> sto_trace (trace_filter_tid tid t ++ create_serialized_trace t (seq_list t)).
Proof.
  intros.
  assert (~ In (tid, seq_point) t).
  { intuition. apply trace_seqlist_seqpoint in H2. apply H1 in H2. auto. } 
  assert (~ In (tid, seq_point) (trace_filter_tid tid t)).
  { unfold trace_filter_tid.
    intuition.
    apply filter_In in H3.
    destruct H3. apply H2 in H3. auto. }
  induction (trace_filter_tid tid t).
  simpl. auto.
  destruct a.
  simpl in H3. apply not_or_and in H3. destruct H3.
  apply IHt0 in H4.
Admitted.
 
Lemma sto_trace_single tid t:
sto_trace ((tid, seq_point) :: t)
-> sto_trace (create_serialized_trace t (seq_list t))
-> sto_trace ((trace_filter_tid tid ((tid, seq_point) :: t)) ++ (create_serialized_trace t (seq_list t))).
Proof.
  intros; simpl.
  rewrite <- beq_nat_refl.
  inversion H.
  induction H.
  
  
(*  intros.
  inversion H; subst; simpl; rewrite <- beq_nat_refl in *.
  inversion H2. 
  1-8, 10: inversion H1. 
  inversion H1; subst.
  simpl.
  rewrite H2. auto.
  assert (trace)

  all: destruct (Nat.eq_dec tid0 tid); subst.
  all: try rewrite <- beq_nat_refl.
  all: try rewrite <- Nat.eqb_neq in n; try rewrite n; auto.
  rewrite H. auto.
  unfold trace_tid_last in H.
  assert (trace_commit_last t0) = 
*)
Admitted.

Lemma is_sto_trace trace:
  sto_trace trace ->
  sto_trace (create_serialized_trace trace (seq_list trace)).
Proof.
  intros.
  induction H; simpl.
  auto.

  apply start_txn_step in H; [ | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H1.
  
  apply read_item_step in H; [ | auto | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H2.

  apply write_item_step with (val := val) in H; [ | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H1.

  apply try_commit_txn_step in H; [ | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H1.

  apply lock_write_item_step in H; [ | auto | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H2.

  apply validate_read_item_step in H; [ | auto ].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H1.

  apply abort_txn_step in H; [ | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H1.

  apply complete_write_item_step in H; [ | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H1.

  apply seq_point_step in H; [ | auto | auto].
  
  rewrite <- beq_nat_refl.
  apply sto_trace_single with (tid0 := tid0) in IHsto_trace.
  unfold trace_filter_tid in IHsto_trace. simpl in IHsto_trace.
  rewrite <- beq_nat_refl in IHsto_trace. unfold trace_filter_tid.
  assert (sto_trace ((tid0, seq_point) :: t)). { auto. }
  apply seq_list_no_two_seqpoint in H. 
  assert (~ In (tid0, seq_point) t -> ~ In tid0 (seq_list t)).
  { intuition. apply trace_seqlist_seqpoint_rev in H4. apply H3 in H4. auto. }
  apply H3 in H.
  apply serial_action_remove with (action0 := seq_point) in H; [ | auto].
   rewrite <- H in IHsto_trace. auto. auto.
  
  apply commit_txn_step in H; [ | auto].
  
  
  
  admit.
Admitted.

(*
Check whether an element a is in the list l
*)
Fixpoint In_bool (a:nat) (l:list nat) : bool :=
  match l with
    | [] => false
    | b :: m => (b =? a) || In_bool a m
  end.

Fixpoint does_not_contain_tid tid (tr:trace) : Prop :=
  match tr with
  | [] => True
  | (tid', _) :: rest => tid <> tid' /\ does_not_contain_tid tid rest
  end.

(*
The function checks if a trace is a serial trace by making sure that
tid is only increaing as we traverse the trace
In this function, we assume that the trace is in the correct order.
That is, the first (tid*action) in the trace is actually the first one that gets to be executed
*)
Function check_is_serial_trace (tr: trace) : Prop :=
  match tr with 
  | [] => True
  | (tid, x) :: rest =>
    match rest with
    | [] => True
    | (tid', y) :: _ => (tid = tid' \/ trace_filter_tid tid rest = [])
                        /\ check_is_serial_trace rest
    end
  end.

Lemma check_app a tr: 
  check_is_serial_trace (a :: tr) -> check_is_serial_trace tr.
Proof.
  intros.
  destruct a. destruct tr.
  auto. destruct p. destruct tr.
  simpl. auto. simpl in H.
  destruct (Nat.eq_dec t0 t).
  subst. rewrite <- beq_nat_refl in H. simpl in *.
  destruct H. auto.
  rewrite <- Nat.eqb_neq in n. rewrite n in H. simpl in *.
  destruct H. auto.
Qed.

Lemma check_split_right tr1 tr2: 
  check_is_serial_trace (tr1 ++ tr2)
  -> check_is_serial_trace tr2. 
Proof.
  intros.
  induction tr1.
  rewrite app_nil_l in H. auto.
  simpl in H. apply check_app in H. apply IHtr1 in H. auto.
Qed.

Eval compute in check_is_serial_trace [(2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (2, read_item 0); (2, start_txn); (3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn)].

Eval compute in check_is_serial_trace [(3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)].

Eval compute in check_is_serial_trace example_txn.

(***************************************************)
Lemma is_serial trace:
  sto_trace trace ->
  check_is_serial_trace (create_serialized_trace trace (seq_list trace)).
Proof.
  intros.
  induction H.
  simpl. auto.
  simpl. apply start_txn_step with (tid0 := tid0) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1. auto.
  simpl. apply read_item_step with (tid := tid0) (val:= val) (oldver:= oldver) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H2. auto. auto.
  simpl. apply write_item_step with (tid := tid0) (oldval:= oldval) (ver:= ver) (val:= val) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1. auto.
  simpl. apply try_commit_txn_step with (tid := tid0) (ver:= ver) (val:= val) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1. auto.
  simpl. apply lock_write_item_step with (tid := tid0) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H2. auto. auto.
  simpl. apply validate_read_item_step with (tid := tid0) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1. auto.
  simpl. apply abort_txn_step with (tid := tid0) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1. auto.
  simpl. apply complete_write_item_step with (tid := tid0) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1. auto.
  simpl. rewrite <- beq_nat_refl.
  
  
Admitted.
(***************************************************)


(*
This function executes STO trace in the reverse order
The goal is to record all read and write actions of all *committed* transactions
*)
Function exec (sto_trace: trace) (commit_tid: list nat) : list (tid * action) :=
  match sto_trace with
  | [] => []
  | (tid, action) :: tail => if (In_bool tid commit_tid)
            then match action with
                | read_item _ => (tid, action) :: exec tail commit_tid
                | write_item _ => (tid, action) :: exec tail commit_tid
                | _ => exec tail commit_tid
                 end
            else exec tail commit_tid
  end.

Eval compute in exec example_txn (seq_list example_txn).

(*
This function returns all values that is written in a trace to a memory location
*)
Function tid_write_value (trace: trace) : list value :=
  match trace with
  | [] => []
  | (_, write_item val) :: tail => val :: tid_write_value tail
  | _ :: tail => tid_write_value tail
  end.

(*
This function returns a list of pair that records write values of each tids in the trace
the first element in a pair is tid
the second element is all the write values written by the transaction with the id tid
*)
Function get_write_value (trace: trace) (tids: list nat) : list (nat * (list value)):=
  match tids with
  | [] => []
  | head :: tail => (head, tid_write_value (trace_filter_tid head trace)) :: get_write_value trace tail
  end.


Definition get_write_value_out (sto_trace: trace) : list (nat * (list value)) :=
  get_write_value sto_trace (seq_list sto_trace).

Eval compute in get_write_value_out example_txn.

(*
This function compares values in two lists one by one
The value at each position in one list should be the same as that in the other list
*)
Function compare_value (ls1: list value) (ls2: list value): bool:=
  match ls1, ls2 with
  | [], [] => true
  | _ , [] => false
  | [], _ => false
  | h1::t1, h2::t2 => if h1=?h2 then compare_value t1 t2 else false
  end.

(*
We compare writes of two traces in this function
If they have the same write sequence, then the function will return True
****************************************************
We assume that two traces have the same tids in the same sequence
Should we actually add tid1 =? tid2 in the code to remove this assumption?
****************************************************
*)
Function compare_write_list (ls1: list (nat * (list value))) (ls2:list (nat * (list value))): Prop :=
  match ls1, ls2 with
  | [], [] => True
  | _ , [] => False
  | [], _ => False
  | (tid1, ver1)::t1, (tid2, ver2)::t2 
        => if (tid1 =? tid2 ) && (compare_value ver1 ver2) then compare_write_list t1 t2
            else False
  end.

Definition write_synchronization trace1 trace2: Prop:=
  compare_write_list (get_write_value_out trace1) (get_write_value_out trace2).

(*
The function returns the last write value of a STO-trace
*)
Definition last_write_value trace: nat:=
  trace_write_last (exec trace (seq_list trace)).

Eval compute in last_write_value example_txn.
(*
Definition write_synchronization trace1 trace2: Prop:=
  if (last_write_value trace1) =? (last_write_value trace2)
  then True
  else False.
*)
Eval compute in write_synchronization example_txn (create_serialized_trace example_txn (seq_list example_txn)).

(*
A STO-trace and its serial trace should have the same writes.
**************************************************
Should we prove that create_serialized_trace function actually prove the correct serial trace of the
STO-trace
**************************************************
*)

(***************************************************)
Lemma write_consistency trace:
  sto_trace trace 
  -> sto_trace (create_serialized_trace trace (seq_list trace))
  -> check_is_serial_trace (create_serialized_trace trace (seq_list trace))
  -> write_synchronization trace (create_serialized_trace trace (seq_list trace)).

Proof.
  intros.
  induction H.
  - unfold write_synchronization; unfold get_write_value_out; simpl; auto.
  - unfold write_synchronization. unfold get_write_value_out.
    assert (seq_list (create_serialized_trace ((tid0, start_txn) :: t) (seq_list ((tid0, start_txn) :: t))) = seq_list t).
    { simpl. apply seq_list_equal2. intuition. inversion H3. }
  rewrite H3.
Admitted.
(***************************************************)

(*
Now we proceed to the read part of the proof.
*)

(*
This function returns the version numbers of all the reads in a trace
*)
Function tid_read_version (trace: trace) : list version :=
  match trace with
  | [] => []
  | (_, read_item ver) :: tail => ver :: tid_read_version tail
  | _ :: tail => tid_read_version tail
  end.

(*
This function groups all versions of reads of a transaction in a trace.
This returns a list of pairs
The first element of a pair is the tid
The second element is a list of all versions of the reads from the transaction tid
*)
Function get_read_version (trace: trace) (tids: list nat) : list (nat * (list version)):=
  match tids with
  | [] => []
  | head :: tail => (head, tid_read_version (trace_filter_tid head trace)) :: get_read_version trace tail
  end.

Definition get_read_version_out (trace: trace) : list (nat * (list version)) :=
  get_read_version trace (seq_list trace).

Eval compute in get_read_version_out example_txn.

Eval compute in get_read_version_out example_txn2.

(*
This function compares all read versions of two list
This is the same as compare all write in previous functions
*)
Function compare_version (ls1: list version) (ls2: list version): bool:=
  match ls1, ls2 with
  | [], [] => true
  | _ , [] => false
  | [], _ => false
  | h1::t1, h2::t2 => if h1=?h2 then compare_version t1 t2 else false
  end.

Function compare_read_list (ls1: list (nat * (list version))) (ls2:list (nat * (list version))): Prop :=
  match ls1, ls2 with
  | [], [] => True
  | _ , [] => False
  | [], _ => False
  | (tid1, ver1)::t1, (tid2, ver2)::t2 
        => if (tid1 =? tid2 ) && (compare_version ver1 ver2) then compare_read_list t1 t2
            else False
  end.

Definition read_synchronization trace1 trace2: Prop:=
  compare_read_list (get_read_version_out trace1) (get_read_version_out trace2).

Eval compute in read_synchronization example_txn (create_serialized_trace example_txn (seq_list example_txn)).

Eval compute in compare_read_list [(1, [0;0]); (2, [1;1])] [(1, [0]);(2, [1;1])].

(*
A STO-trace and its serial trace should have the same reads.
*)

(***************************************************)
Lemma read_consistency trace:
  sto_trace trace 
  -> sto_trace (create_serialized_trace trace (seq_list trace))
  -> is_serial_trace (create_serialized_trace trace (seq_list trace))
  -> read_synchronization trace (create_serialized_trace trace (seq_list trace)).
Admitted.
(***************************************************)

(*
Two traces can be considered equivalent in execution if they produce the same reads and writes
*)
Definition Exec_Equivalence trace1 trace2: Prop:=
  write_synchronization trace1 trace2 /\ read_synchronization trace1 trace2.

Eval compute in Exec_Equivalence example_txn (create_serialized_trace example_txn (seq_list example_txn)).

(*
The capstone theorem: prove serializability of a sto-trace
*)
Theorem txn_equal t:
  sto_trace t
  -> exists t', sto_trace t'
  -> is_serial_trace t'
  -> Exec_Equivalence t t'.
Proof.
  exists (create_serialized_trace t (seq_list t)).
  intros. 
  unfold Exec_Equivalence. split.
  apply write_consistency; auto.
  apply read_consistency; auto.
Qed.
  