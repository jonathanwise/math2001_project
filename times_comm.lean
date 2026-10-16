import natural_numbers
import zero_times
import times_zero
import succ_times
import times_succ

theorem times_comm ( m n : ℕ )
: m * n = n * m := by
  induction m using ℕ.rec
  case zero =>
    rewrite[zero_times]
    rewrite[times_zero]
    rfl
  case succ m ih =>
    rewrite[succ_times]
    rewrite[times_succ]
    rewrite[ih]
    rfl
