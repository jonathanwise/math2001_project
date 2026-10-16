import natural_numbers
import zero_times
import times_zero
import succ_times
import times_succ
import times_right_distrib

theorem times_assoc ( m n p : ℕ )
: m * ( n * p ) = ( m * n ) * p := by
  induction m using ℕ.rec
  case zero =>
    rewrite[zero_times]
    rewrite[zero_times]
    rfl
  case succ m ih =>
    rewrite[succ_times]
    rewrite[succ_times]
    rewrite[times_right_distrib]
    rewrite[ih]
    rfl
