import natural_numbers
import zero_times
import plus_zero


theorem succ_times ( m n : ℕ )
: m.succ * n = n + m * n := by
  conv => lhs ; unfold times
  
