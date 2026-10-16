import natural_numbers
import zero_times

theorem times_zero ( m : ℕ )
: m * ℕ.zero = ℕ.zero := by
  induction m
  case zero =>
    rewrite [zero_times] -- this is just zero times zero so can use zero_times
    rfl
  case succ m ih =>
    unfold times -- unfold the recursive case of times
    rewrite [ih] -- we get m * zero as part of the left hand side, this is just zero from ih
    unfold plus -- unfolds plus to solve zero + zero
    rfl
