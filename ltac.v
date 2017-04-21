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
  apply in_or_app. right. simpl. auto.
  remove_unrelevant_last_txn.
  rewrite n in H4. 
  apply IHsto_trace in H4. 
  apply in_or_app. left. auto.
Qed.

Lemma trace_seqlist_seqpoint t tid:
  In (tid, seq_point) t
  -> In tid (seq_list t).
Proof.
  intros.
  functional induction seq_list t.
  inversion H.
  destruct (Nat.eq_dec tid tid0); subst; apply in_or_app. 
  right. simpl. auto.
  left. apply IHl. apply in_inv in H. destruct H.
  inversion H. apply Nat.eq_sym in H1. contradiction. auto.
  all: destruct (Nat.eq_dec tid tid0); subst; apply IHl; apply in_inv in H; destruct H; try inversion H; auto.
Qed.

Lemma seq_list_no_two_seqpoint t tid:
  sto_trace ((tid, seq_point) :: t)
  -> ~ In (tid, seq_point) t.
Proof.
  intros.
  assert (sto_trace t). { apply sto_trace_app with (tid0 := tid) (action0 := seq_point). auto. }
  inversion H.
  intuition.

  all: unfold trace_no_seq_points in H4; apply in_split in H6;
  destruct H6; destruct H6;
  rewrite H6 in H4; simpl in H4;
  rewrite trace_filter_tid_app in H4;
  simpl in H4;
  rewrite <-beq_nat_refl in H4;
  rewrite map_app in H4;
  rewrite Forall_app in H4;
  destruct H4; simpl in H7;
  apply Forall_inv in H7; simpl in H7; auto.
Qed.
