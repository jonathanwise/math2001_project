import natural_numbers
import functions
import plus_comm
import succ_inj
import plus_cancel_left

private def g : ℕ → ℕ
| a => 1 + a

example : injective g := by
  unfold injective
  intro a b gab
  change 1+a=1+b at gab
  have h1 := plus_cancel_left a b 1 gab
  exact h1
