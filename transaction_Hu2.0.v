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
|validate_read_item: Prop -> action
|abort_txn: Prop -> action (*True means abort needs to unlock before abort, False means the transaction about to be aborted does not contain locks*)
(*|restart_txn: action*)
|complete_write_item: (*value -> action*)version -> action
(*|unlock_write_item: version -> action*)
(*|invalid_write_item: value -> action*)
|commit_txn: action
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
(*
Definition trace_filter_commit tr: trace :=
    filter (fun pr => match snd pr with
                      | commit_txn => true
                      | _ => false
                      end) tr.
*)
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
Returns all complete_write actions in the trace for updating version number of reads
*)
Definition trace_filter_complete tr: trace :=
    filter (fun pr => match snd pr with
                      | complete_write_item _ => true
                      | _ => false
                      end) tr.

(*
Returns the last action of the transaction tid
Returns dummy if there is no transaction with id tid.
*)
Definition trace_tid_last tid t: action :=
    hd dummy (map snd (trace_filter_tid tid t)).

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

(*
Returns the version number of the last commit
If there is no commit in the trace, returns 0.
*)
(*
Definition trace_commit_last t: version :=
  match hd dummy (map snd (trace_filter_commit t)) with
	| commit_txn n => n
	| _ => 0
  end.
*)
(*
Returns the value of the last write
If there is no write in the trace, returns 0.
*)
(*
PROBLEMATIC: last write cannot be 0 in this case.
SUGGESTION: Use "option"
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
(*
Definition trace_commit_complete_last t: version :=
  match hd dummy (map snd (trace_filter_commit_complete t)) with
	| commit_txn n => n
  | complete_write_item n => n
	| _ => 0
  end.
*)

Definition trace_complete_last t: version :=
  match hd dummy (map snd (trace_filter_complete t)) with
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
                      | complete_write_item _ => true
                      | abort_txn True => true
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

Definition action_no_read e : Prop :=
  match e with
  | read_item _ => False
  | _ => True
  end.

(*
Returns true if an action is not a commit_txn action
Returns false if an action is a commit_txn action.
*)
Definition action_no_commit e : Prop :=
  match e with
  | commit_txn => False
  | _ => True
  end.

Definition action_no_seq_point e: Prop:=
    match e with
  | seq_point => False
  | _ => True
  end.

Definition action_is_lock e: Prop:=
    match e with
  | lock_write_item => True
  | _ => False
  end.
(*
Returns true if the transaction tid's trace has no writes
Returns false otherwise.
*)
Definition trace_no_writes tid t: Prop :=
  Forall action_no_write (map snd (trace_filter_tid tid t)).

Definition trace_no_reads tid t: Prop :=
  Forall action_no_read (map snd (trace_filter_tid tid t)).


(*
Returns true if the transaction tid's trace has no commits
Returns false otherwise.
*)
Definition trace_no_commits tid t: Prop :=
  Forall action_no_commit (map snd (trace_filter_tid tid t)).

Definition trace_no_seq_points tid t: Prop :=
  Forall action_no_seq_point (map snd (trace_filter_tid tid t)).

Definition trace_has_locks tid t: Prop :=
  Forall action_is_lock (map snd (trace_filter_tid tid t)).

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
(*
Definition trace_filter_startreadwrite tid tr: trace :=
    filter (fun pr => (fst pr =? tid) &&
                      (match snd pr with
                      | read_item _ => true
                      | write_item _ => true
                      | start_txn => true
                      | _ => false
                      end)) tr.
*)
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
    -> sto_trace ((tid, read_item (trace_complete_last t)) :: t)

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
      ~ trace_no_writes tid t
      -> check_lock_or_unlock t
			-> trace_tid_last tid t = try_commit_txn
			-> sto_trace t
			-> sto_trace ((tid, lock_write_item) :: t)

| validate_read_item_step: forall t tid,
      ~ trace_no_reads tid t
			-> (trace_tid_last tid t = try_commit_txn /\ trace_no_writes tid t ) (*read only*)
			\/ trace_tid_last tid t = lock_write_item (*/\ ~ trace_no_writes tid t*)(*lock write*)
			-> sto_trace t
			-> sto_trace ((tid, validate_read_item (check_version (read_versions_tid tid t)  (trace_complete_last t) ))::t)
(*
<<<<<<<<<<<<<<<<<<<>>>>>>>>>>>>>>>>>>>
The other abort condition is not included here
If when trying to lock memory location to write (in lock_write_item_step), there already exists a lock on that location,
then the transaction should be aborted: lock_write_item -> abort
The other similar situation that is not encoded is: read_item -> abort

THIS MODEL IS NOT COMPLETE

*)
| abort_txn_step: forall t tid,
      trace_tid_last tid t = validate_read_item False 
      -> sto_trace t
      -> sto_trace ((tid, abort_txn (trace_has_locks tid t)) :: t) (*abort will contain unlock....*)

(*sequential point*)
| seq_point_step: forall t tid,
      (trace_tid_last tid t = validate_read_item True (*/\ ~ trace_no_reads tid t*))
      \/ (trace_tid_last tid t = lock_write_item /\ trace_no_reads tid t)
      (*-> trace_no_commits tid t*)
      -> trace_no_seq_points tid t
      -> sto_trace t
      -> sto_trace ((tid, seq_point) :: t)
| complete_write_item_step: forall t tid,
      ~ trace_no_writes tid t
      -> trace_tid_last tid t = seq_point
      -> sto_trace t
      -> sto_trace ((tid, complete_write_item (S (trace_complete_last t))) :: t)
| commit_txn_step: forall t tid ver,
      (trace_tid_last tid t = seq_point /\ trace_no_writes tid t)
      \/ (trace_tid_last tid t = complete_write_item ver)
      -> sto_trace t
      -> sto_trace ((tid, commit_txn) :: t).

Hint Constructors sto_trace.

Definition example_txn:=
[(2, commit_txn); (2, complete_write_item 1); (2, seq_point); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (2, read_item 0); (2, start_txn); (1, commit_txn); (1, seq_point); (1, validate_read_item True); (1, try_commit_txn); (1, read_item 0); (1, start_txn)].

Definition example_txn2:=
[(3, commit_txn); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn False); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn); (2, complete_write_item 1); (2, seq_point); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)].


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
  | (tid, abort_txn _) :: tail => seq_list tail
  | (tid, complete_write_item n) :: tail => seq_list tail
  | (tid, commit_txn) :: tail => seq_list tail
  end.

Eval compute in seq_list example_txn.

Eval compute in seq_list example_txn2.

Function create_serialized_trace (sto_trace: trace) (seqls : list nat): trace:=
  match seqls with
  | [] => []
  | head :: tail 
    => trace_filter_tid head sto_trace ++ create_serialized_trace sto_trace tail
  end.

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
Two traces can be considered equivalent in execution if they produce the same reads and writes
*)
Definition Exec_Equivalence trace1 trace2: Prop:=
  write_synchronization trace1 trace2 /\ read_synchronization trace1 trace2.

Eval compute in Exec_Equivalence example_txn (create_serialized_trace example_txn (seq_list example_txn)).


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
  destruct H6. destruct H3.
  rewrite H3 in H4. simpl in H4.
  rewrite trace_filter_tid_app in H4.
  simpl in H4.
  rewrite <-beq_nat_refl in H4. 
  rewrite map_app in H4.
  rewrite Forall_app in H4.
  destruct H4. simpl in H6. 
  apply Forall_inv in H6. simpl in H6. auto.
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
  -> action = commit_txn \/ action = complete_write_item (S (trace_complete_last (t1 ++ (tid, seq_point) :: t2))).
Proof.
  intros.
  induction t1.
  simpl in H.
  - inversion H; subst.
    -- simpl in H2. rewrite <- beq_nat_refl in H2. inversion H2.
    -- unfold trace_tid_last in H3. simpl in H3. rewrite <- beq_nat_refl in H3. repeat destruct or H3; inversion H3.
    -- unfold trace_tid_last in H2. simpl in H2. rewrite <- beq_nat_refl in H2. repeat destruct or H2; inversion H2.
    -- unfold trace_tid_last in H2. simpl in H2. rewrite <- beq_nat_refl in H2. repeat destruct or H2; inversion H2.
    -- unfold trace_tid_last in H5. simpl in H5. rewrite <- beq_nat_refl in H5. inversion H5.
    -- unfold trace_tid_last in H4. simpl in H4. rewrite <- beq_nat_refl in H4. destruct H4. destruct H0. simpl in H0. inversion H0. simpl in H0. inversion H0.
    -- unfold trace_tid_last in H2. simpl in H2. rewrite <- beq_nat_refl in H2. inversion H2.
    -- unfold trace_tid_last in H3. simpl in H3. rewrite <- beq_nat_refl in H3. destruct H3. inversion H0. inversion H0. inversion H1.
    -- unfold trace_tid_last in H4. simpl in H4. rewrite <- beq_nat_refl in H4. simpl in *. right. auto.
    -- auto.
  - destruct a. destruct a.
    -- destruct (Nat.eq_dec tid t); subst; apply sto_trace_app in H; inversion H.
    -- destruct (Nat.eq_dec tid t); subst.
  admit.
Admitted.

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

Lemma seq_list_seq tid t:
  sto_trace t -> 
  trace_tid_last tid t = seq_point
  -> In tid (seq_list t).
Proof.
  intros.
  induction H; simpl; try discriminate.
  1, 3-4, 7, 10 : remove_unrelevant_last_txn; rewrite n in H3; apply IHsto_trace in H3; auto.
  1, 3, 5: remove_unrelevant_last_txn; rewrite n in H4; apply IHsto_trace in H4; auto.
  1: remove_unrelevant_last_txn; rewrite n in H5; apply IHsto_trace in H5; auto.
  remove_unrelevant_last_txn.
  left. auto.
  rewrite n in H4. 
  apply IHsto_trace in H4. 
  right. auto.
Qed.

Lemma same_version v1 v2:
  complete_write_item v1 = complete_write_item v2
  -> v1 = v2.
Admitted.

Lemma seq_list_complete tid t ver:
  sto_trace t -> 
  trace_tid_last tid t = complete_write_item ver
  -> In tid (seq_list t).
Proof.
  intros.
  induction H; simpl; try discriminate.
  1, 3-4, 7, 10 : remove_unrelevant_last_txn; rewrite n in H3; apply IHsto_trace in H3; auto.
  1, 3, 4: remove_unrelevant_last_txn; rewrite n in H4; apply IHsto_trace in H4; auto.
  1: remove_unrelevant_last_txn; rewrite n in H5; apply IHsto_trace in H5; auto.
  remove_unrelevant_last_txn.
  simpl in *. rewrite <- beq_nat_refl in H0; simpl in *.
  apply seq_list_seq in H1. auto. auto.
  rewrite n in H4.
  apply IHsto_trace in H4. myauto.
Qed.

Lemma seq_point_before_commit (t:trace) (tid: tid):
  sto_trace ((tid, commit_txn) :: t) ->
  In (tid, seq_point) t.
Proof.
  intros.
  inversion H.
  destruct H2.
  destruct H2.
  apply seq_list_seq in H2.
  apply trace_seqlist_seqpoint_rev in H2.
  auto. auto.
  apply seq_list_complete in H2.
  apply trace_seqlist_seqpoint_rev in H2.
  auto. auto.
Qed.

Lemma seq_point_before_complete (t:trace) (tid: tid):
  sto_trace ((tid, complete_write_item (S (trace_complete_last t))) :: t) ->
  In (tid, seq_point) t.
Proof.
  intros.
  inversion H.
  apply seq_list_seq in H4.
  apply trace_seqlist_seqpoint_rev in H4.
  auto. auto.
Qed.

Lemma seq_list_action tid action t:
  sto_trace ((tid, action) :: t) -> 
  action = seq_point \/ action = commit_txn \/ action = complete_write_item (S (trace_complete_last t))
  <-> In tid (seq_list ((tid, action) :: t)).
Proof.
  split.
  intros. destruct H0.
  apply seq_list_seqpoint; auto.
  subst. inversion H; subst.
  simpl.
  1-8: destruct H0; inversion H0.
  simpl. apply seq_list_seq in H5. auto. auto.
  destruct H3. destruct H1. simpl. 
  apply seq_list_seq in H1; auto.
  apply seq_list_complete in H1; auto.
  
  intros.
  apply trace_seqlist_seqpoint_rev in H0.
  apply in_inv in H0.
  destruct H0.
  inversion H0. left. auto.
  right.
  apply in_split in H0. destruct H0. destruct H0. rewrite H0 in *.
  apply seq_point_after in H. auto.
Qed.



Lemma seq_list_action_neg tid action t:
  sto_trace ((tid, action) :: t) -> 
  action <> seq_point /\ action <> commit_txn /\ action <> complete_write_item (S (trace_complete_last t))
  <-> ~ In tid (seq_list ((tid, action) :: t)).
Proof.
  intros. split. 
  intros. 
  intuition.
  apply seq_list_action in H .
  destruct H. apply H3 in H1. 
  destruct H1; auto. destruct H1; auto. 

  intros.
  intuition.
  apply seq_list_action in H .
  destruct H.
  assert (action = seq_point \/ action = commit_txn \/ action = complete_write_item (S (trace_complete_last t))). { left. auto. }
  apply H in H3. auto.
  apply seq_list_action in H .
  destruct H.
  assert (action = seq_point \/ action = commit_txn \/ action = complete_write_item (S (trace_complete_last t))). { right. left.  auto. }
  apply H in H3. auto.
  apply seq_list_action in H .
  destruct H.
  assert (action = seq_point \/ action = commit_txn \/ action = complete_write_item (S (trace_complete_last t))). { right. right.  auto. }
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
  action <> seq_point /\ action <> commit_txn /\ action <> complete_write_item (S (trace_complete_last t))
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
  apply serial_action_remove with (action0 := read_item (trace_complete_last t)) in H1; [auto | auto].

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
     (check_version (read_versions_tid tid t) (trace_complete_last t))) in H1; [auto | auto].

  apply seq_list_action_neg in H. destruct H. apply H in H0.
  apply seq_list_not_seqpoint2 in H1; [ | auto ].
  apply serial_action_remove with (action0 := abort_txn (trace_has_locks tid t)) in H1; [auto | auto].

  destruct H0. congruence.
  destruct H0. destruct H3. congruence.
  destruct H0. destruct H3. congruence.
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
  sto_trace ((tid, commit_txn) :: t)
  -> t = t1 ++ (tid, seq_point) :: t2
  -> create_serialized_trace ((tid, commit_txn) :: t) (seq_list ((tid, commit_txn) :: t)) = 
  create_serialized_trace t (seq_list t1) ++ (tid, commit_txn) :: trace_filter_tid tid t ++ create_serialized_trace t (seq_list t2).
Proof.
  intros.
  assert (~ In tid (seq_list t2)).
  
Admitted.


Lemma serial_action_before_complete tid t1 t2 t:
  sto_trace ((tid, complete_write_item (S (trace_complete_last t))) :: t)
  -> t = t1 ++ (tid, seq_point) :: t2
  -> create_serialized_trace ((tid, complete_write_item (S (trace_complete_last t))) :: t) (seq_list ((tid, complete_write_item (S (trace_complete_last t))) :: t)) = 
  create_serialized_trace t (seq_list t1) ++ (tid, complete_write_item (S (trace_complete_last t))) :: trace_filter_tid tid t ++ create_serialized_trace t (seq_list t2).
Proof.
  intros.
  assert (~ In tid (seq_list t2)).
  
Admitted.

Lemma seq_list_equal trace:
  sto_trace trace -> 
  seq_list (create_serialized_trace trace (seq_list trace)) = seq_list trace.
Proof.
  intros. simpl.
  induction H; simpl.
  auto.
  apply start_txn_step with (tid0 := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1. auto.
  apply read_item_step with (tid := tid0) (val:= val) (oldver:= oldver) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H2; inversion H. auto. auto.
  apply write_item_step with (tid := tid0) (ver:= ver) (oldval:= oldval) (val := val) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1; inversion H. auto.
  apply try_commit_txn_step with (tid := tid0) (ver:= ver) (val:= val) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1; inversion H. auto.
  apply lock_write_item_step with (tid := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H3. auto. auto. auto.
  apply validate_read_item_step with (tid := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H2. auto. auto.
  apply abort_txn_step with (tid := tid0) in H0. apply serial_action_helper in H0. rewrite <- H0 in IHsto_trace. auto. split; intuition; inversion H1. auto. 

  rewrite <- beq_nat_refl. simpl.
  apply seq_point_step with (tid:= tid0) in H1.
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
  
  apply complete_write_item_step with (tid := tid0) in H0; [ | auto | auto].
  assert (sto_trace t). { apply sto_trace_app in H0. auto. }
  assert (sto_trace ((tid0, complete_write_item (S (trace_complete_last t))) :: t)). { auto. }
  apply seq_point_before_complete in H0.
  apply in_split in H0. destruct H0. destruct H0.
  assert (t = x ++ (tid0, seq_point) :: x0). { auto. }
  assert (t = x ++ (tid0, seq_point) :: x0). { auto. }
  apply serial_action_before_complete in H0; [ | auto].
  simpl in H0.
  unfold tid in H0. rewrite H0.
  rewrite seq_list_split_no_seqpoint. simpl.
  apply serial_action_split in H4; [ | auto].
  rewrite <- IHsto_trace. rewrite H4. rewrite H5.
  rewrite <- seq_list_split_no_seqpoint. auto.
  
  apply commit_txn_step with (tid := tid0) (ver:= ver) in H0; [ | auto].
  assert (sto_trace t). { apply sto_trace_app in H0. auto. }
  assert (sto_trace ((tid0, commit_txn) :: t)). { auto. }
  apply seq_point_before_commit in H0.
  apply in_split in H0. destruct H0. destruct H0.
  assert (t = x ++ (tid0, seq_point) :: x0). { auto. }
  assert (t = x ++ (tid0, seq_point) :: x0). { auto. }
  apply serial_action_before_commit in H0; [ | auto].
  simpl in H0.
  unfold tid in H0. rewrite H0.
  rewrite seq_list_split_no_seqpoint. simpl.
  apply serial_action_split in H4; [ | auto].
  rewrite <- IHsto_trace. rewrite H4. rewrite H3.
  rewrite <- seq_list_split_no_seqpoint. auto.

Qed.

(*
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
 *)

Lemma sto_trace_single tid t:
  sto_trace ((tid, seq_point) :: t)
  -> sto_trace (create_serialized_trace t (seq_list t))
  -> sto_trace ((trace_filter_tid tid ((tid, seq_point) :: t)) ++ (create_serialized_trace t (seq_list t))).
Proof.
  intros; simpl.
  rewrite <- beq_nat_refl.
  inversion H.
  induction H.
  
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

  apply lock_write_item_step in H; [ | auto | auto | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H3.

  apply validate_read_item_step in H; [ | auto| auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H2; inversion H0.

  apply abort_txn_step in H; [ | auto].
  apply serial_action_helper in H. simpl in H. rewrite <- H in IHsto_trace. auto. split; intuition; inversion H1.

  rewrite <- beq_nat_refl.
  apply seq_point_step in H; [ | auto | auto].
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

  apply complete_write_item_step in H; [ | auto | auto].
  admit.
  
  apply commit_txn_step in H; [ | auto].
  
  
  
  admit.
Admitted.

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
(*
Eval compute in check_is_serial_trace [(2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (2, read_item 0); (2, start_txn); (3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn)].

Eval compute in check_is_serial_trace [(3, commit_txn 1); (3, seq_point); (3, validate_read_item True); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item False); (1, try_commit_txn); (2, commit_txn 1); (2, seq_point); (2, complete_write_item 1); (2, validate_read_item True); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0);  (2, start_txn); (1, start_txn)].
*)
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
  simpl. apply read_item_step with (tid := tid0) (val:= val) (oldver:= oldver) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H2; inversion H. auto. auto.
  simpl. apply write_item_step with (tid := tid0) (oldval:= oldval) (ver:= ver) (val:= val) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1; inversion H. auto.
  simpl. apply try_commit_txn_step with (tid := tid0) (ver:= ver) (val:= val) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1; inversion H. auto.
  simpl. apply lock_write_item_step with (tid := tid0) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H3; inversion H. auto. auto. auto.
  simpl. apply validate_read_item_step with (tid := tid0) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H2; inversion H. auto. auto.
  simpl. apply abort_txn_step with (tid := tid0) in H0. rewrite serial_action_helper; auto. split; intuition; inversion H1. auto.
  simpl. rewrite <- beq_nat_refl.
  apply seq_point_step with (tid := tid0) in H1; [ | auto| auto].
  assert (sto_trace ((tid0, seq_point) :: t)). { auto. }
  apply seq_list_no_two_seqpoint in H1. 
  assert (~ In (tid0, seq_point) t -> ~ In tid0 (seq_list t)).
  { intuition; apply trace_seqlist_seqpoint_rev in H4; apply H3 in H4; auto. }
  apply H3 in H1.
  apply serial_action_remove with (action0 := seq_point) in H1; [ | auto].
  admit.

  simpl. apply complete_write_item_step with (tid := tid0) in H0; [ | auto | auto].
  admit.
  
  simpl. apply commit_txn_step with (tid := tid0) (ver:= ver) in H0; [ | auto].
  admit.
  
Admitted.
(***************************************************)

Lemma write_sync_list_unchanged_noseq :
  forall t tid a, sto_trace ((tid, a)::t) ->
  a = start_txn ->
  get_write_value_out t = get_write_value_out ((tid, a)::t).
Proof.
  intros.
  unfold get_write_value_out.
  subst. simpl.
  induction (seq_list t).
  simpl. auto.
  simpl.
  destruct (Nat.eq_dec tid0 a).
  - subst. rewrite <- beq_nat_refl. rewrite IHl. intuition.
  - rewrite <- Nat.eqb_neq in n. rewrite n. rewrite IHl. auto.
Qed.

Lemma write_sync_list_unchanged_noseq2 :
  forall t tid a, sto_trace ((tid, a)::t) ->
  a <> seq_point ->
  get_write_value_out t = get_write_value_out ((tid, a)::t).
Proof.
  intros.
  unfold get_write_value_out.
  subst. destruct a. simpl.
  induction (seq_list t).
  simpl. auto.
  simpl.
  destruct (Nat.eq_dec tid0 a).
  - subst. rewrite <- beq_nat_refl. rewrite IHl. intuition.
  - rewrite <- Nat.eqb_neq in n. rewrite n. rewrite IHl. auto.
Qed.

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
A STO-trace and its serial trace should have the same reads.
*)

(***************************************************)
Lemma read_consistency trace:
  sto_trace trace 
  -> read_synchronization trace (create_serialized_trace trace (seq_list trace)).
Admitted.
(***************************************************)

(*
The capstone theorem: prove serializability of a sto-trace
*)
Theorem txn_equal t:
  sto_trace t
  -> exists t', sto_trace t'
  -> check_is_serial_trace t'
  -> Exec_Equivalence t t'.
Proof.
  exists (create_serialized_trace t (seq_list t)).
  intros. 
  unfold Exec_Equivalence. split.
  apply write_consistency; auto.
  apply read_consistency; auto.
Qed.
  