import natural_numbers

theorem zero_times ( n : ℕ )
: ℕ.zero * n = ℕ.zero := by
  unfold times
  rfl
