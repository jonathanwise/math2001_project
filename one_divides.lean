import natural_numbers
import times_one

theorem one_divides ( n : ℕ )
: divides 1 n := by
  unfold divides
  apply Exists.intro n
  exact times_one n
