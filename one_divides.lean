import natural_numbers
import times_one

theorem one_divides ( n : ℕ )
: divides 1 n := by
    unfold divides
    exists n
    rewrite [times_one]
    rfl
