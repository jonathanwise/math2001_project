import functions
import compose_id_then_first_injective
import compose_id_then_second_surjective

theorem has_inverse_then_bijective { S T : Type }
{ f : S → T } { g : T → S }
( h_gf : g ∘ f = id ) ( h_fg : f ∘ g = id )
: bijective f := by
  unfold bijective
  apply And.intro
  case left =>
    unfold injective
    intro a b fab
    have h1 : g (f a) = g (f b) := congrArg g fab
    have ha : g (f a) = a :=congrFun h_gf a
    have hb : g (f b) = b :=congrFun h_gf b
    rw [ha, hb] at h1
    exact h1
  case right =>
    unfold surjective
    intro t
    apply Exists.intro (g t)
    have fgt : f (g t) = t := congrFun h_fg t
    exact fgt
