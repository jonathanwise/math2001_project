import natural_numbers
import functions
import plus_comm
import succ_inj
import plus_succ
import plus_zero
import zero_not_succ
import zero_plus

private def g : ℕ → ℕ
| a => 1 + a

example : ¬ surjective g := by
  intro hsurj
  unfold surjective at hsurj
  have h := hsurj 0
  cases h with
  | intro y hy =>
    unfold g at hy
    rw [plus_comm] at hy
    have h1 : y + 1 = y.succ := by
      have h2 : y + 0 = y := plus_zero y
      have h3 := plus_succ y 0
      rw [h2] at h3
      exact h3
    rw [h1] at hy
    have h2 := zero_not_succ y
    have h3 := hy.symm
    contradiction
