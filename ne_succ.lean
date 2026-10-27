import natural_numbers
import peano

theorem ne_succ ( n : ℕ )
: n ≠ n.succ := by
  intro nEns
  cases nEns
