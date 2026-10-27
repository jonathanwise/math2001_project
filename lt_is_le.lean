import natural_numbers

theorem lt_is_le {m n : ℕ} : (m < n) → (m ≤ n) := by
  intro mltn
  unfold lt at mltn
  have ⟨ mlen, notm ⟩ := mltn
  exact mlen
