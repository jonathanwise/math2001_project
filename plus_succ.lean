import natural_numbers

import zero_plus

theorem plus_succ ( m n : ℕ )
: m + n.succ = (m + n).succ := by
  induction m
  case zero =>
    rewrite [zero_plus] -- gets rid of zeros here
    rewrite [zero_plus] -- and here
    rfl -- to get n.succ = n.succ
  case succ m ih =>
    unfold plus -- applies recursive case of addition to both sides of the equation
    rewrite [ih] -- uses ih to rewrite the left side to be the same as the right side
    rfl
