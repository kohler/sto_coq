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
Definition value := Z.
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
|complete_write_item: value -> action
|invalid_write_item: value -> action
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
			(trace_tid_last tid t = try_commit_txn /\ trace_no_writes tid t )
			\/ trace_tid_last tid t = lock_write_item
			-> sto_trace t
			-> sto_trace ((tid, validate_read_item (check_version (read_versions_tid tid t)  (trace_commit_last t) ))::t).