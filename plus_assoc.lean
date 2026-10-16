import natural_numbers
import zero_plus
import succ_plus

theorem plus_assoc ( m n p : ℕ )
: m + ( n + p ) = ( m + n ) + p := by
  induction m -- proving with induction on m
  case zero =>
    rewrite [zero_plus] -- turns 0 + (n + p) into n + p
    rewrite [zero_plus] -- turns 0 + n into n
    rfl -- now we have n + p = n + p
  case succ m ih =>
    rewrite [succ_plus] -- turns m.succ + (n + p) into (m + (n + p)).succ
    rewrite [succ_plus] -- turns m.succ + n + p into (m + n).succ + p
    rewrite [succ_plus] -- turns (m + n).succ + p into (m + n + p).succ
    rewrite [ih] -- we can use the ih to now make both sides equal
    rfl
