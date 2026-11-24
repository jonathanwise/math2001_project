import parity

theorem even_or_odd (n : ℕ)
: is_even n ∨ is_odd n := by
  induction n -- doing this by standard induction on n
  case zero =>
    apply Or.inl -- proving that zero is even
    unfold is_even -- 0 % 2 = 0 so rfl
    rfl
  case succ n ih =>
    unfold is_even -- unfolding even and odd
    unfold is_odd
    cases ih -- splitting into two cases, one for even one for odd
    case inl ih =>
      unfold is_even at ih -- previous step was an even number
      apply Or.inr -- we will prove the successor is odd
      unfold remainder -- unfolds the remainder functionality
      rewrite [ih] -- turns r into 1 using the previous step
      rfl -- r is not equal to 2 so this comes out to 1, need to show 1=1 so rfl
    case inr ih =>
      unfold is_odd at ih -- previous step was an odd number
      apply Or.inl -- we will prove the successor is even
      unfold remainder -- unfolds the remainder functionality
      rewrite [ih] -- turns r into 2 using the previous step
      rfl -- r is 2 in this case so we get the whole thing equal to 0, need to show 0=0 so rfl
