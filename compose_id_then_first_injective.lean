import functions

theorem compose_id_then_first_injective { S T : Type }
  { f : S → T } { g : T → S }
  ( h : g ∘ f = id )
  : injective f := by
  unfold injective
  intro a b
  intro hf
  have hgf : g (f a) = g (f b) := congrArg g hf
  have ha : g (f a) = a := congrFun h a
  have hb : g (f b) = b := congrFun h b
  rw [ha, hb] at hgf
  exact hgf
