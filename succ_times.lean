import natural_numbers

theorem succ_times ( m n : ℕ )
: m.succ * n = n + m * n := by
  conv => lhs ; unfold times
  
