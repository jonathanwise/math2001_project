import natural_numbers
import times_comm
import zero_times
import plus_zero

theorem times_one (n:ℕ) : n*1 = n := by
  rewrite[times_comm]
  show ℕ.succ ℕ.zero * n = n
  rewrite[succ_times]
  rewrite[zero_times]
  rewrite[plus_zero]
  rfl
