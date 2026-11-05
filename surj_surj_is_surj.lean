import functions

theorem surj_surj_is_surj { S T U : Type } { f : S → T } { g : T → U }
( hf : surjective f ) ( hg : surjective g )
: surjective ( g ∘ f ) := by
<<<<<<< HEAD
  unfold surjective
  intro u
  unfold surjective at hg
  unfold surjective at hf
  have h1 : ∃ t, g t = u := by
    apply hg
  rcases h1 with ⟨t, ht⟩
  have h2 : ∃ s, f s = t := by
    apply hf
  rcases h2 with ⟨s, hs⟩
  apply Exists.intro s
  change g (f s) = u
  rewrite [hs]
  exact ht
=======
  intro u
  cases hg u with
  | intro t ht =>
    cases hf t with
    | intro s hs =>
      exact ⟨s, show g (f s) = u by rw [hs, ht]⟩
>>>>>>> upstream/main
