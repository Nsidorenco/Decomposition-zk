require import AllCore List.

lemma bound_range (n m : int) :
  all (fun i => n <= i < m) (range n m).
proof.
  rewrite allP.
  move=> x.
  simplify.
  rewrite /range mema_iota.
  by rewrite addzCA subzz.
qed.

lemma foldr_range b (f : int -> bool -> bool) n m:
    foldr f b (range n m) = foldr (fun i acc => n <= i < m /\ f i acc) b (range n m).
proof.
  have := bound_range n m.
  elim (range n m).
  - progress.
  - progress.
  have -> : (n <= x && x < m) = true by rewrite H0 H1.
  simplify.
  rewrite H. apply H2.
  done.
qed.

lemma foldr_id (b : 'b) (xs : 'a list):
    foldr (fun i acc => acc) b xs = b.
proof.
   elim xs; progress.
qed.
 
op folding_op (N : int) (f : int -> bool) =
  (foldr (fun i acc, acc /\ f i)
    true (range 0 N)).

pred forall_op (N : int) (f : int -> bool) =
    forall i, 0 <= i < N => f i.

(* Helper lemma*)
lemma foldr_false (N : int) f :
  foldr (fun (i : int) (acc : bool) => acc /\ f i) false (range 0 N) = false.
proof.
  elim /natind N.
  - progress. rewrite range_geq. assumption. done.
  - progress.
    rewrite rangeSr. assumption.
    rewrite -cats1.
    rewrite foldr_cat.
    simplify.
    by rewrite H0.
qed.
    

(* Helper Lemma *)
lemma op_reflect N f : folding_op N f = forall_op N f.
proof.
  rewrite /folding_op /forall_op.
  elim /natind N.
  - progress. rewrite range_geq. assumption. smt().
  - progress.
    rewrite rangeSr. assumption.
    rewrite -cats1.
    rewrite foldr_cat.
    simplify.
    have -> : (forall (i : int), 0 <= i && i < n + 1 => f i) <=> (forall (i : int), 0 <= i && i < n => f i) /\ f n.
    - progress.
      smt().
      smt().
      smt().
    case (f n); progress.
    by rewrite foldr_false.
qed.

