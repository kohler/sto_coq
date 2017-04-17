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
    trace_tid_last tid t = dummy (* this tid doesn’t have start_txn*)
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
      -> trace_no_commits tid t
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

Definition example_txn:=
[(2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (2, read_item 0); (2, start_txn); (1, commit_txn 0); (1, seq_point); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (1, start_txn)].

Definition example_txn2:=
[(3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)].

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

(*
This function creates a serialized trace.
Just like STO-trace, the order is reversed: that is, the first (tid*action) pair in the serial trace
constructed by this function is the last operation performed in this trace
*)
Function create_serialized_trace (sto_trace: trace) (seqls : list nat): trace:=
  match seqls with
  | [] => []
  | head :: tail 
    => create_serialized_trace sto_trace tail ++ trace_filter_tid head sto_trace
  end.

Eval compute in create_serialized_trace example_txn (seq_list example_txn).

Eval compute in create_serialized_trace example_txn2 (seq_list example_txn2).

Lemma serial_seqlist_equal trace:
  sto_trace trace ->
  seq_list trace = seq_list (create_serialized_trace trace (seq_list trace)).
  intros. induction H.
  - simpl. auto.
  - simpl. 

(*
This lemma proves that the seq_point of each transaction in a STO-trace determines its serialized order in the serial trace
*)
Lemma seq_list_equal tid action trace:
  action = seq_point <->
  seq_list (create_serialized_trace ((tid, action) :: trace) (seq_list ((tid, action) :: trace))) = seq_list trace ++ [tid].
Proof.
  split.
  intros. subst. 
  simpl. 
  - 
    Search ( _ =? _ ).
Admitted.

(*
This lemma proves that the sequences of other actions in each transaction in a STO-trace does not
affect its order in the serial trace
*)
Lemma seq_list_equal2 tid action trace:
  ~(action = seq_point) ->
  seq_list (create_serialized_trace ((tid, action) :: trace) (seq_list trace)) = seq_list trace.
Proof.
Admitted.

(*
Check whether an element a is in the list l
*)
Fixpoint In_bool (a:nat) (l:list nat) : bool :=
  match l with
    | [] => false
    | b :: m => (b =? a) || In_bool a m
  end.

(*
The function checks if a trace is a serial trace by making sure that
tid is only increaing as we traverse the trace
In this function, we assume that the trace is in the correct order.
That is, the first (tid*action) in the trace is actually the first one that gets to be executed
*)
Function check_is_serial_trace (tr: trace) (tidls: list nat): Prop :=
  match tr with 
  | [] => True
  | (tid, _) :: tail => if (negb (tid =? (hd 0 tidls))) && (In_bool tid tidls)
                          then False
                          else check_is_serial_trace tail (tid :: tidls)
  end.

Definition is_serial_trace tr: Prop :=
  check_is_serial_trace (rev tr) [].

Eval compute in is_serial_trace [(2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (2, read_item 0); (2, start_txn); (3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn)].

Eval compute in is_serial_trace [(3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)].

Eval compute in is_serial_trace example_txn.


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

Lemma serialized_trace_app_no_sp:
  forall t tid a, sto_trace t -> a <> seq_point -> 
    create_serialized_trace t (seq_list t) = 
    create_serialized_trace ((tid, a)::t) (seq_list ((tid, a)::t)).
Proof.
  intros.
  assert (seq_list t = seq_list ((tid0, a) :: t)) by (induction a; simpl; intuition).
  rewrite <- H1.
  assert (~ In tid0 (seq_list t)). {
  inversion H. Focus 2.
  remember (seq_list t) as splist. clear H1. clear Heqsplist.
  functional induction (create_serialized_trace ((tid0, a) :: t) splist).
  -- auto.
  -- simpl. assert (tid0 =? head = false). admit. 
     rewrite H1. admit.


(*
A STO-trace and its serial trace should have the same writes.
**************************************************
Should we prove that create_serialized_trace function actually prove the correct serial trace of the
STO-trace
**************************************************
*)
 Lemma write_equivalence trace:
  sto_trace trace -> 
  let serialized_trace := create_serialized_trace trace (seq_list trace) in
  write_synchronization trace serialized_trace.

Proof.
  intros.
  induction H.
  - unfold write_synchronization. unfold get_write_value_out. simpl. auto.
  - unfold write_synchronization. 
    unfold write_synchronization in IHsto_trace.
    assert (get_write_value_out t = get_write_value_out ((tid0, start_txn) :: t)).
    { unfold get_write_value_out. simpl. clear H. clear serialized_trace.
      unfold get_write_value_out in IHsto_trace. simpl in IHsto_trace.
      assert (seq_list (create_serialized_trace t (seq_list t)) = seq_list t). admit.
      rewrite H in IHsto_trace. clear H. remember (seq_list t) as tids. clear Heqtids.
      functional induction (get_write_value t tids).
      -- simpl. auto.
      -- 
 simpl. destruct (Nat.eq_dec tid0 head).
         --- admit. (* This case is not possible. skip for now *)
         --- apply Nat.eqb_neq in n. rewrite n.
             assert (get_write_value t tail = get_write_value ((tid0, start_txn) :: t) tail). 
             { remember ((head, tid_write_value (trace_filter_tid head t))
                 :: get_write_value t tail) as ls1.
               remember (get_write_value (create_serialized_trace t (head :: tail))
                   (head :: tail)) as ls2.
               functional induction (compare_write_list ls1 ls2).
                ---- inversion Heqls2.
                ---- discriminate.
                ---- discriminate.
                ---- assert (t1 <> (head, tid_write_value (trace_filter_tid head t))
         :: get_write_value t tail). admit. admit.
                ---- auto. intuition. } admit. }
      rewrite serialized_trace.
                     
assert (create_serialized_trace t (head :: tail) == create_serialized_trace t tail).
 
 simpl in *.

  - unfold write_synchronization. unfold get_write_value_out.
    assert (seq_list (create_serialized_trace ((tid0, start_txn) :: t) (seq_list ((tid0, start_txn) :: t))) = seq_list t).
    {
      remember (start_txn) as action. 
      apply seq_list_equal2. rewrite Heqaction. intuition. inversion H2. 
    }
  
  rewrite H3.
Admitted.*)

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
Lemma read_consistency trace:
  sto_trace trace 
  -> sto_trace (create_serialized_trace trace (seq_list trace))
  -> is_serial_trace (create_serialized_trace trace (seq_list trace))
  -> read_synchronization trace (create_serialized_trace trace (seq_list trace)).
Admitted.

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
  