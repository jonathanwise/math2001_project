import functions

theorem compose_id_then_second_surjective { S T : Type }
  { f : S → T } { g : T → S }
  ( h : g ∘ f = id )
  : surjective g := by
  unfold surjective
  intro t
  apply Exists.intro (f t)
  have ht: g (f t) = t := congrFun h t
  exact ht
