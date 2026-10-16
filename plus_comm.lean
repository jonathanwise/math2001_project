import natural_numbers
import zero_plus
import plus_zero
import succ_plus
import plus_succ

theorem plus_comm ( m n : ℕ )
: m + n = n + m := by
  induction m using ℕ.rec
  case zero =>
    rewrite[zero_plus]
    rewrite[plus_zero]
    rfl
  case succ m ih =>
    rewrite[succ_plus]
    rewrite[plus_succ]
    rewrite[ih]
    rfl
