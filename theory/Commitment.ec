(* Formalization of Commitment schemes *)
require import AllCore Distr DBool.
(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

type public_key.
type secret_key.
type commitment.
type message.
type randomness.

op dm : {message distr | is_lossless dm} as dm_ll.
op dr : {randomness distr | is_lossless dr} as dr_ll.


op valid_key (key : secret_key * public_key) : bool.
op verify (m : message) (c : commitment) : bool.

module type Committer = {
  proc commit(m : message) : commitment
}.


module Correctness(C : Committer) = {
  proc main(m : message) : bool = {
    var c, b;
    c <- C.commit(m);
    b <- verify m c;
    return b;
  }
}.

module BindingGame(C : Committer) = {
  proc main(c : commitment, m1 m2 : message) = {
    var v1, v2;
    v1 <- verify m1 c;
    v2 <- verify m2 c;
    return v1 /\ v2 /\ (m1 = m2);
  }

  proc bind_three(c1, c2, c3, m1 m1' m2 m2' m3 m3' : message) = {
    var v1, v2, v3;
    v1 <- main(c1, m1, m1');
    v2 <- main(c2, m2, m2');
    v3 <- main(c3, m3, m3');
    return v1 /\ v2 /\ v3;
  }
}.

