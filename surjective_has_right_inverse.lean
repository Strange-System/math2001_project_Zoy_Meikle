import functions

open Classical
theorem surjective_has_right_inverse { S T : Type } { f : S → T }
: surjective f → ∃ (g : T → S), f ∘ g = id
:= by
  intro h
  unfold surjective at h
  let g (t : T ) := choose ( h t )
  have hg ( t : T ) := choose_spec ( h t )
  apply Exists.intro g
  funext t
  unfold compose
  unfold id
  exact hg t
