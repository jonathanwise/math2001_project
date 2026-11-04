import natural_numbers

namespace ℕ
theorem two_step_induction {P: ℕ → Prop}
( h0 : P 0 )
( h1 : P 1 )
( step : (n:ℕ) → P n → P n.succ → P n.succ.succ )
: ∀ (n:ℕ), P n
:= by
  have lemma : ∀ (n : ℕ) , P n ∧ P n.succ := by
    intro n
    induction n with
    | zero =>
      exact ⟨h0, h1⟩
    | succ n ih =>
      have h2 : P n.succ.succ := by
        exact step n ih.1 ih.2
      exact ⟨ih.2, h2⟩
  intro n
  obtain h3 := lemma n
  exact h3.1
end ℕ
