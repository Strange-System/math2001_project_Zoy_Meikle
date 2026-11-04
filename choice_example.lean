

open Classical
example { S : Type } { P : S → Prop } { Q : Prop }
( h : ∃ (x : S), P x ) ( h' : ∀ (x : S), ( P x → Q ) )
: Q := by
  let h : ∃ (x : S) := choose ( x : S )
  sorry
