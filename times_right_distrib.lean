import natural_numbers
import zero_plus
import zero_times
import succ_plus
import succ_times
import plus_assoc

theorem times_right_distrib ( m n p : ℕ )
: (m + n ) * p = m*p + n*p := by
  induction m using ℕ.rec
  case zero =>
    rewrite[zero_plus,zero_times]
    rfl
  case succ m ih =>
    rewrite[succ_plus,succ_times,ih,succ_times,plus_assoc]
    rfl
