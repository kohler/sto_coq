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
|restart_txn: action
|complete_write_item: (*value -> action*)version -> action
|unlock_write_item: version -> action
(*|invalid_write_item: value -> action*)
|commit_txn: version -> action
|obtain_global_tid: action.

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
Returns all lock_write_item actions in the trace.
*)
Definition trace_filter_lock tr: trace :=
    filter (fun pr => match snd pr with
                      | lock_write_item => true
                      | _ => false
                      end) tr.

(*
Returns all unlock_write_item actions in the trace.
*)
Definition trace_filter_unlock tr: trace :=
    filter (fun pr => match snd pr with
                      | unlock_write_item _ => true
                      | _ => false
                      end) tr.

Function length (tr: trace) : nat := 
  match tr with 
  | [] => 0
  | _ :: tr' => S (length tr')
  end.
(*
Returns T if there exists lock_write_item
*)
Definition check_lock_or_unlock tr: Prop :=
  match 
    length (trace_filter_lock tr) =? length (trace_filter_unlock tr)  
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
Returns true if the transaction tid's trace has no writes
Returns false otherwise.
*)
Definition trace_no_writes tid t: Prop :=
  Forall action_no_write (map snd (trace_filter_tid tid t)).

(*
Returns all read_item actions in a trace of a particular transaction.
*)
Function read_versions tr: list version :=
  match tr with
   | [] => []
   | (read_item v) :: tail =>  v :: read_versions tail
   | _ :: tail => read_versions tail
  end.

(*
Returns all read_item actions of tid in a trace tr.
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
			-> sto_trace t
			-> sto_trace ((tid, lock_write_item) :: t)

| validate_read_item_step: forall t tid,
			(trace_tid_last tid t = try_commit_txn /\ trace_no_writes tid t ) (*read only*)
			\/ trace_tid_last tid t = lock_write_item (*lock write*)
			-> sto_trace t
			-> sto_trace ((tid, validate_read_item (check_version (read_versions_tid tid t)  (trace_commit_last t) ))::t)

(*new added...*)
| abort_txn_step: forall t tid,
      trace_tid_last tid t = validate_read_item False (*invalid*)
      -> sto_trace t
      -> sto_trace ((tid, abort_txn) :: t)
      
| complete_write_item_step: forall t tid,
			trace_tid_last tid t = validate_read_item True (*valid read*)
      /\ ~ trace_no_writes tid t
      -> sto_trace t
      -> sto_trace ((tid, complete_write_item (S (trace_commit_last t))) :: t)

| unlock_write_item_step: forall t tid ver,
      trace_tid_last tid t = complete_write_item ver
			/\ ~ trace_no_writes tid t (*locked*)
      -> sto_trace t
      -> sto_trace ((tid, unlock_write_item ver) :: t)

| commit_readonly_txn_step: forall t tid,
      (trace_tid_last tid t = validate_read_item True /\ trace_no_writes tid t)(*read only*)
      -> sto_trace t
      -> sto_trace ((tid, commit_txn (trace_commit_last t)) :: t)

| commit_write_txn_step: forall t tid ver,
      trace_tid_last tid t = unlock_write_item ver(*unlock the write*)
      -> sto_trace t
      -> sto_trace ((tid, commit_txn ver) :: t)

| restart_txn_step: forall t tid,
      trace_tid_last tid t = abort_txn (*we get abort and then restart*)
      -> sto_trace t
    (*our restart is to add back*)
      -> sto_trace ((trace_filter_tid tid t) ++ t).
    (*but !!! we need to change the tid for old ones*)

Example example1:  
sto_trace [(2, commit_txn 1); (2, unlock_write_item 1); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, commit_txn 0); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (2, start_txn); (1, start_txn)].

apply commit_write_txn_step.
unfold trace_tid_last. simpl. auto.

apply unlock_write_item_step.
unfold trace_tid_last. simpl. split. auto.
unfold trace_no_writes. simpl.
admit.
(*apply Exists_Forall_neg.*)
assert (trace_commit_last ([(2, validate_read_item True);
  (2, lock_write_item); (2, try_commit_txn); (2, write_item 4);
  (1, commit_txn 0); (1, validate_read_item True); (1, try_commit_txn);
  (1, read_item 0); (2, start_txn); (1, start_txn)]) = 0).
{ unfold trace_commit_last. simpl. auto. }
assert (1 = S (trace_commit_last
      [(2, validate_read_item True); (2, lock_write_item);
      (2, try_commit_txn); (2, write_item 4); (1, commit_txn 0);
      (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0);(2, start_txn); (1, start_txn)])).
{ rewrite H. auto. }
rewrite H0.

apply complete_write_item_step; rewrite <-H0.
unfold trace_tid_last. simpl. split. auto.
unfold trace_no_writes. simpl.
admit.
clear H H0.
assert (
  (check_version (read_versions_tid 2 
([(2, lock_write_item); (2, try_commit_txn);
  (2, write_item 4); (1, commit_txn 0); (1, validate_read_item True);
  (1, try_commit_txn); (1, read_item 0); (2, start_txn); (1, start_txn)])
)  
  (trace_commit_last 
([(2, lock_write_item); (2, try_commit_txn);
  (2, write_item 4); (1, commit_txn 0); (1, validate_read_item True);
  (1, try_commit_txn); (1, read_item 0); (2, start_txn); (1, start_txn)])
) = True)).
  {unfold check_version. simpl. auto. }
  rewrite <- H.

apply validate_read_item_step; rewrite H. 
unfold trace_tid_last. simpl. right. auto. clear H.

apply lock_write_item_step. split.
unfold trace_tid_last. simpl. auto.
unfold trace_no_writes. simpl.
admit.

apply try_commit_txn_step with (ver := 0) (val:= 4).
unfold trace_tid_last. simpl. auto.

apply write_item_step with (ver:=0) (oldval:=0).
unfold trace_tid_last. simpl. left. auto.
assert ((trace_commit_last ([(1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (2, start_txn); (1, start_txn)])) = 0).
{ unfold trace_commit_last. simpl. auto. }
rewrite <- H. 

apply commit_readonly_txn_step; rewrite H. 
unfold trace_tid_last. simpl. split. auto.
admit.
clear H.
assert (
  (check_version (read_versions_tid 1 
([(1, try_commit_txn); (1, read_item 0);
  (2, start_txn); (1, start_txn)])
) (trace_commit_last 
([(1, try_commit_txn); (1, read_item 0);
  (2, start_txn); (1, start_txn)])
) = True)).
  {unfold check_version. simpl. auto. } 
  rewrite <- H.

apply validate_read_item_step.
unfold trace_tid_last. simpl. left. split. auto.
admit.
clear H.

apply try_commit_txn_step with (ver:= 0) (val:= 0).
unfold trace_tid_last. simpl. left. auto.

assert (trace_commit_last [(2, start_txn); (1, start_txn)] = 0).
{unfold trace_commit_last; simpl. auto. }
rewrite <- H.

apply read_item_step with (val:=0) (oldver:=0); rewrite H. clear H.
unfold trace_tid_last. simpl. left. auto.
unfold check_lock_or_unlock. simpl. auto.

apply start_txn_step. unfold trace_tid_last. auto.
apply start_txn_step. unfold trace_tid_last. auto.

apply empty_step.









