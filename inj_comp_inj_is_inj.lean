import functions

theorem inj_comp_inj_is_inj {S T U : Type} (f : S → T) (g : T → U)
: injective f ∧ injective g → injective ( g ∘ f )
:= by
  intro h -- injective f ^ injective g as true
  rcases h with ⟨hf, hg⟩ -- seperate injective f and injective g
  intro x z h_eq -- h_eq is (gf)x = (gf)z, goal is x = z
  have hf_eq := hf h_eq -- f x = f z
  exact hf hf_eq -- x = z
