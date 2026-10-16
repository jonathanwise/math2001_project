import natural_numbers
import times_zero
import plus_zero
import plus_assoc
import plus_comm
import succ_times

theorem times_succ ( m n : ℕ )
: m * n.succ = m + m * n := by
  induction m
  case zero =>
    unfold times
    unfold plus
    rfl
  case succ m ih =>
    rewrite [succ_times, succ_times]
    rewrite[ih]
    rewrite[plus_assoc, plus_assoc]
    rewrite[succ_plus, succ_plus]
    rewrite [plus_comm n m]
    rewrite[succ_plus]
    rewrite[succ_plus]
    rfl
