import natural_numbers
import functions
import plus_comm
import succ_inj

-- private def g : ℕ → ℕ
-- | a => 1 + a

private def g (n : ℕ) := n + 1

example : injective g := by
 unfold injective
 intro a b
 unfold g
 intro h
 rewrite [plus_comm] at h
 change a.succ = b+1 at h
 rewrite [plus_comm] at h
 change a.succ = b.succ at h
 apply succ_inj
 exact h
