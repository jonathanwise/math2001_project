import natural_numbers
import succ_inj
import zero_plus
import succ_plus

theorem eq_plus_same_is_zero {m n : ℕ} : m + n = m → n = 0 := by
  induction m
  case zero =>
    intro h
    have h1 : ℕ.zero + n = n := by
      unfold plus
      change n=n
      rfl
    rw [h1] at h
    exact h
  case succ m ih =>
    intro h
    have h1 : m.succ + n = (m + n).succ := succ_plus (m := m) (n := n)
    rewrite [h1] at h
    have h2 : (m+n).succ = m.succ → m+n = m := succ_inj
    have h3 := h2 h
    have h4 := ih h3
    exact h4
    
