import functions

theorem surj_surj_is_surj { S T U : Type } { f : S → T } { g : T → U }
( hf : surjective f ) ( hg : surjective g ) 
: surjective ( g ∘ f ) := by
  intro u
  obtain ⟨t, ht⟩ := hg u
  obtain ⟨s, hs⟩ := hf t
  use s 
  /- you are using a MathLib tactic that isn't
  available in class; try rewriting this with
  Exists.intro -/
  exact ht ▸ hs
