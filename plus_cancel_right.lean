import plus_zero
import plus_succ
import succ_inj

theorem plus_cancel_right {m n : ℕ} (k:ℕ)
: m + k = n + k → m = n := by
  induction k using ℕ.rec
  case zero =>
    intro h
    rewrite[plus_zero, plus_zero] at h
    exact h

  case succ k ih =>
    intro h
    rewrite[plus_succ, plus_succ] at h
    have h2 := succ_inj h
    rewrite[ih]
    rfl
    exact h2
    
