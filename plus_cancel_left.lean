import plus_cancel_right
import plus_comm

theorem plus_cancel_left (m n k : ℕ)
: k + m = k + n → m = n := by
  -- Introduce hypothesis
  intro h
  -- Rewrite left and right side of h with commutativity of addition
  rewrite[plus_comm k m, plus_comm k n] at h
  -- Finish proof by using plus_cancel_right (I did this right before)
  exact plus_cancel_right k h
