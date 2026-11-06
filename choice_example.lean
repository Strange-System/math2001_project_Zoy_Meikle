

open Classical
example { S : Type } { P : S → Prop } { Q : Prop }
( h : ∃ (x : S), P x ) ( h' : ∀ (x : S), ( P x → Q ) )
: Q := by
  let x : S := choose h
  have hx : P x := choose_spec h
  exact h' x hx
