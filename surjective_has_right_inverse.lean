import functions

open Classical
theorem surjective_has_right_inverse { S T : Type } { f : S → T }
: surjective f → ∃ (g : T → S), f ∘ g = id
:= by
  intro h
  unfold surjective at h
  let g (t : T) := choose (h t) -- h t : ∃ y, f y = t
  -- let s ∈ S be an element
  have hg (t : T) := choose_spec (h t)
  -- such that f(s) = t
  apply Exists.intro g
  funext t -- for every input they have the same output
  unfold compose
  unfold id
  exact hg t
