import natural_numbers
import zero_times

theorem divides_zero (n : ℕ)
: divides n 0 := by
  unfold divides
  apply Exists.intro 0
  exact zero_times n
