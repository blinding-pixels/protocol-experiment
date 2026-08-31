require import AllCore.

(* The paper writes ceil(log_2 n).  Rather than importing floating-point or an
   unconstrained loss operator, [h] is required to be the unique nonnegative
   integer whose power-of-two interval contains positive [n]. *)
op beekem_is_ceil_log2 (n h : int) : bool =
     1 <= n
  /\ 0 <= h
  /\ n <= 2 ^ h
  /\ (h = 0 \/ (1 <= h /\ 2 ^ (h - 1) < n)).

op beekem_theorem1_loss (c h : int) : real =
  c%r * h%r.

lemma beekem_ceil_log2_one : beekem_is_ceil_log2 1 0.
proof. by rewrite /beekem_is_ceil_log2; smt(). qed.

lemma beekem_ceil_log2_two : beekem_is_ceil_log2 2 1.
proof. by rewrite /beekem_is_ceil_log2; smt(). qed.
