### Lemmas
- If a trace is a `sto_trace`, removing the last action in the trace (i.e., the first element in the trace) generates a new `sto_trace`.
```
Lemma sto_trace_app tid action t:
  sto_trace ((tid, action) :: t) -> sto_trace t.
```

- If a trace is a `sto_trace`, removing several of its last actions (i.e., first several elements in the trace) generates a new `sto_trace`.
```
Lemma sto_trace_app2 t1 t2:
  sto_trace (t1 ++ t2) -> sto_trace t2.
```

- In a `sto_trace`, if the last action in the trace with its transaction id `tid` is not `seq_point` and `tid` is not in the sequential list, then `tid` is not in the sequential list even after removing that last action
```
Lemma seq_list_not_seqpoint tid action t:
  sto_trace ((tid, action) :: t) ->
  action <> seq_point ->
  ~ In tid (seq_list ((tid, action) :: t))
  -> ~ In tid (seq_list t).
```

- In a `sto_trace`, if its sequential list does not contain `tid`, then `tid` is not in the sequential list even after removing the last action of the trace
```
Lemma seq_list_not_seqpoint2 tid action t:
  sto_trace ((tid, action) :: t) ->
  ~ In tid (seq_list ((tid, action) :: t))
  -> ~ In tid (seq_list t).
```

- If the last action in a `sto_trace` is `seq_point`, then the `tid` associated with that action should be in the sequential list of the trace
```
Lemma seq_list_seqpoint tid action t:
  sto_trace ((tid, action) :: t) ->
  action = seq_point ->
  In tid (seq_list ((tid, action) :: t)).
```

- Any `tid`s that have `seq_point` in the trace should also be in the sequential list of that trace
```
Lemma trace_seqlist_seqpoint t tid:
  In (tid, seq_point) t
  -> In tid (seq_list t).
```

- If a `tid` is in the sequential list of the trace, then that `tid` must have a `seq_point` action in that trace
```
Lemma trace_seqlist_seqpoint_rev t tid:
  In tid (seq_list t)
  -> In (tid, seq_point) t.
```

- Fact about `filter` function
```
Lemma filter_app (f: nat * action -> bool) l1 l2:
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
```

- Fact about `trace_filter_tid` function
```
Lemma trace_filter_tid_app tid tr1 tr2:
  trace_filter_tid tid (tr1 ++ tr2) =
  trace_filter_tid tid tr1 ++ trace_filter_tid tid tr2.

```

- Fact about `Forall` function
```
Lemma Forall_app (P: action -> Prop) l1 l2:
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
```

- A transaction `tid` should not have two `seq_point` actions in a `sto_trace`
```
Lemma seq_list_no_two_seqpoint t tid:
  sto_trace ((tid, seq_point) :: t)
  -> ~ In (tid, seq_point) t.
```

- If `seq_point` action associated with a transaction `tid` has appeared in a `sto_trace`, it should not appear again later in the same trace
```
Lemma seq_list_no_two_seqpoint2 t1 t2 tid:
  sto_trace (t1 ++ (tid, seq_point) :: t2)
  -> ~ In (tid, seq_point) t1.
```

- In a `sto_trace`, if there is a `seq_point` associated with a transaction `tid`, then there must be a `commit_txn` associated with the same `tid` later in the trace. *ADMITTED*
```
Lemma seq_point_after t1 t2 tid action:
  sto_trace ((tid, action) :: t1 ++ (tid, seq_point) :: t2)
  -> action = commit_txn (trace_commit_complete_last (t1 ++ (tid, seq_point) :: t2)).
```

- In a `sto_trace`, if `tid` is in its sequential list, then the last action of that transaction in the trace cannot be `start_txn`
```
Lemma seq_list_last_tid_start_txn tid t:
  sto_trace t ->
  In tid (seq_list t) ->
  trace_tid_last tid t <> start_txn.
```

- In a `sto_trace`, if the last action of a transaction `tid` is `seq_point` action, then this `tid` must be in the sequential list of that trace
```
Lemma seq_list_commit tid t:
  sto_trace t ->
  trace_tid_last tid t = seq_point
  -> In tid (seq_list t).
```

- In a `sto_trace`, if a transaction `tid` has a `commit_txn` action, then it must have a `seq_point` action in the trace before that the `seq_point` action
```
Lemma seq_point_before_commit (t:trace) (tid: tid) n:
  sto_trace ((tid, commit_txn n) :: t) ->
  In (tid, seq_point) t.
```

- In a `sto_trace`, if a transaction `tid` has a `seq_point` action in the trace, then its next action must be `commit_txn` action.
```
Lemma seq_point_before_commit2 t tid action:
  sto_trace ((tid, action) :: t) ->
  In (tid, seq_point) t ->
  action = commit_txn (trace_commit_complete_last t).
```

- If a transaction `tid` has either a `seq_point` or a `commit_txn` action in a `sto_trace`, then `tid` must also be in the sequential list of that trace, and vice versa.
```
Lemma seq_list_action tid action t:
  sto_trace ((tid, action) :: t) ->
  action = seq_point \/ action = commit_txn (trace_commit_complete_last t)
  <-> In tid (seq_list ((tid, action) :: t)).
```

- If a transaction `tid` has neither a `seq_point` nor a `commit_txn` action in a `sto_trace`, then this `tid` must not be in the sequential list of that trace, and vice versa.
```
Lemma seq_list_action_neg tid action t:
  sto_trace ((tid, action) :: t) ->
  action <> seq_point /\ action <> commit_txn (trace_commit_complete_last t)
  <-> ~ In tid (seq_list ((tid, action) :: t)).
```

- In a `sto_trace`, if a transaction `tid` does not have `seq_point` action in the trace, then adding all actions belonging to `tid` in this trace to another trace does not change the sequential list of that trace
```
Lemma seqlist_filter t t' tid:
  sto_trace t
  -> ~ In (tid, seq_point) t
  -> seq_list (trace_filter_tid tid t ++ t') = seq_list t'.
```

- Fact about `seq_list` function
```
Lemma seq_list_split_no_seqpoint t1 t2:
  seq_list (t1 ++ t2) = seq_list t1 ++ seq_list t2.

Lemma seq_list_split_with_seqpoint t1 tid t2:
  seq_list (t1 ++ (tid, seq_point) :: t2) = seq_list t1 ++ tid :: (seq_list t2).
```

- If a `sto_trace` does not have `tid` in its sequential list, then the serial trace of that `sto_trace` created from the sequential list does not change even if a new action belonging to `tid` is added to the `sto_trace` (since it is the sequential list that determines the serial trace).  
```
Lemma serial_action_remove tid action t:
  sto_trace ((tid, action) :: t) ->
  ~ In tid (seq_list t) ->
  create_serialized_trace ((tid, action) :: t) (seq_list t)= create_serialized_trace t (seq_list t).
```

- For a given `sto_trace`, its serial trace does not change if an action other than `seq_point` and `commit_txn` is added to the trace. *Ltac Needed*
```
Lemma serial_action_helper tid action t:
  sto_trace ((tid, action) :: t) ->
  action <> seq_point /\ action <> commit_txn (trace_commit_complete_last t)
  -> create_serialized_trace ((tid, action) :: t) (seq_list ((tid, action) :: t)) =
     create_serialized_trace t (seq_list t).
```

- If a `seq_point` action of a `tid` is added to a `sto_trace`, then the serial trace of the new `sto_trace` must be the serial trace of the old `sto_trace` with all actions of `tid` appended after it
```
Lemma serial_action_helper2 tid t:
  sto_trace ((tid, seq_point)::t)
  -> create_serialized_trace ((tid, seq_point)::t) (seq_list ((tid, seq_point)::t)) = trace_filter_tid tid ((tid, seq_point)::t) ++ create_serialized_trace t (seq_list t).
```

- If adding an action of `tid` to a `sto_trace` does not change the sequential list of the trace, then doing so does not change the serial trace of that trace either
```
Lemma serial_action_seq_list tid action t:
  sto_trace ((tid, action) :: t) ->
  ~ In tid (seq_list ((tid, action) :: t))
  -> create_serialized_trace ((tid, action) :: t) (seq_list ((tid, action) :: t)) = create_serialized_trace t (seq_list t).
```

- All actions belonging to a `tid` in a `sto_trace` are included in its serial trace if `seq_point` action of that `tid` is included in the `sto_trace`
```
Lemma serial_action_split tid t t1 t2:
  sto_trace t
  -> t = t1 ++ (tid, seq_point) :: t2
  -> create_serialized_trace t (seq_list t) =
  create_serialized_trace t (seq_list t1) ++ trace_filter_tid tid ((t1 ++ (tid, seq_point) :: t2)) ++ create_serialized_trace t (seq_list t2).
```

- *Is the following lemma true?*
```
Lemma serial_action_before_commit tid t1 t2 t:
  sto_trace t
  -> t = t1 ++ (tid, seq_point) :: t2
  -> create_serialized_trace ((tid, commit_txn (trace_commit_complete_last t)) :: t) (seq_list ((tid, commit_txn (trace_commit_complete_last t)) :: t)) =
  create_serialized_trace t (seq_list t1) ++ (tid, commit_txn (trace_commit_complete_last t)) :: trace_filter_tid tid t ++ create_serialized_trace t (seq_list t2).
```

- For a `sto_trace`, its sequential list and the sequential list of its serial trace is the same *Ltac Needed*
```
Lemma seq_list_equal trace:
  sto_trace trace ->
  seq_list (create_serialized_trace trace (seq_list trace)) = seq_list trace.
```

- In a `sto_trace`, if a transaction `tid` is not in the sequential list of the trace, then appending all actions belonging to `tid` after the serial trace of the original trace creates a new `sto_trace` *ADMITTED, BUT WHY DO WE NEED THIS?*
```
Lemma serial_action_add tid t:
  sto_trace t
  -> sto_trace (create_serialized_trace t (seq_list t))
  -> ~ In tid (seq_list t)
  -> sto_trace (trace_filter_tid tid t ++ create_serialized_trace t (seq_list t)).
```

- If a `tid` in a `sto_trace` has a `seq_point` action at the end of the trace, then its serial trace must have all actions belonging to `tid` appended at the end
*ADMITTED, BUT WHY ARE WE PROVING STO_TRACE?*
```
Lemma sto_trace_single tid t:
  sto_trace ((tid, seq_point) :: t)
  -> sto_trace (create_serialized_trace t (seq_list t))
  -> sto_trace ((trace_filter_tid tid ((tid, seq_point) :: t)) ++ (create_serialized_trace t (seq_list t))).
```

- The serial trace of a `sto_trace` should also be a `sto_trace` *ADMITTED*
```
Lemma is_sto_trace trace:
  sto_trace trace ->
  sto_trace (create_serialized_trace trace (seq_list trace)).
```

- If a trace is a serial trace, then removing its last action does not change this fact
```
Lemma check_app a tr:
  check_is_serial_trace (a :: tr) -> check_is_serial_trace tr.
```

- If a trace is a serial trace, then removing its several last action does not change this fact
```
Lemma check_split_right tr1 tr2:
  check_is_serial_trace (tr1 ++ tr2)
  -> check_is_serial_trace tr2.
```

- `create_serialized_trace` function on a `sto_trace` actually creates a serial trace *ADMITTED*
```
Lemma is_serial trace:
  sto_trace trace ->
  check_is_serial_trace (create_serialized_trace trace (seq_list trace)).
```

- A `sto_trace` and its serial trace should have the same global write effects *ADMITTED*
```
Lemma write_consistency trace:
  sto_trace trace
  -> sto_trace (create_serialized_trace trace (seq_list trace))
  -> check_is_serial_trace (create_serialized_trace trace (seq_list trace))
  -> write_synchronization trace (create_serialized_trace trace (seq_list trace)).
```

- A `sto_trace` and its serial trace should have the same global read effects *ADMITTED. Use is_serial_trace instead of check_is_serial_trace?*
```
Lemma read_consistency trace:
  sto_trace trace
  -> sto_trace (create_serialized_trace trace (seq_list trace))
  -> is_serial_trace (create_serialized_trace trace (seq_list trace))
  -> read_synchronization trace (create_serialized_trace trace (seq_list trace)).
```

- *Capstone theorem* A `sto_trace` should have a corresponding serial trace that affects the state of the machine in the same manner. 
```
Theorem txn_equal t:
  sto_trace t
  -> exists t', sto_trace t'
  -> is_serial_trace t'
  -> Exec_Equivalence t t'.
```
