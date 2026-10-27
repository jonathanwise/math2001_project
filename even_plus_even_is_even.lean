import even_plus_is_same_parity

theorem even_plus_even_is_even (m n : ℕ)
: is_even m ∧ is_even n → is_even (m + n)
:= by
  intro evenEven
  have ⟨ mEven, nEven ⟩ := evenEven
  rewrite [is_even, divides] at mEven nEven
  rewrite [is_even, divides]
  have ⟨ m1, mDef ⟩ := mEven
  have ⟨ n1, nDef ⟩ := nEven
  rewrite [← nDef, ← mDef]
  


  sorry
