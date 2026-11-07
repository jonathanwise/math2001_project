import natural_numbers
import times_comm
import times_one

theorem one_times (n : ℕ) : 1 * n = n := by
  rewrite[times_comm]
  rewrite[times_one]
  rfl
