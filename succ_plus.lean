import natural_numbers
import plus_zero
import plus_succ

theorem succ_plus ( n : ℕ )
: m.succ + n = (plus m n).succ := by
  conv =>
    lhs
    unfold plus
    rfl
