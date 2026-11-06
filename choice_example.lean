

open Classical
#print choice
#print Nonempty
#print indefiniteDescription
example { S : Type } { P : S → Prop } { Q : Prop }
( h : ∃ (x : S), P x ) ( h' : ∀ (x : S), ( P x → Q ) )
: Q := by
  let a := choose (h)
  have pa := choose_spec (h)
  have pxq := h' a
  have hq := pxq pa
  exact hq
