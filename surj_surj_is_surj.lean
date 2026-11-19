import functions

theorem surj_surj_is_surj { S T U : Type } { f : S → T } { g : T → U }
( hf : surjective f ) ( hg : surjective g )
: surjective ( g ∘ f ) := by
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
