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
 

