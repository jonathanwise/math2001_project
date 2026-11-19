import natural_numbers

namespace ℕ
theorem two_step_induction {P: ℕ → Prop}
( h0 : P 0 )
( h1 : P 1 )
( step : (n:ℕ) → P n → P n.succ → P n.succ.succ )
: ∀ (n:ℕ), P n
:= by
  have lemma : ∀ (n : ℕ) , P n ∧ P n.succ := by -- create lemma that basically step antecedent is true
    intro n
    induction n with
    | zero =>
      exact ⟨h0, h1⟩ -- proved by base cases
    | succ n ih =>
      have h2 : P n.succ.succ := by -- we have that the consequent is true by step and our ih (which originally came from lemma)
        exact step n ih.1 ih.2
      exact ⟨ih.2, h2⟩
  -- now with lemma solved we can finish of easily
  intro n
  obtain h3 := lemma n -- use n to get rid of universal quantifier from lemma
  exact h3.1 -- have answer from first element in conjuction of h3 (lemma)
end ℕ
