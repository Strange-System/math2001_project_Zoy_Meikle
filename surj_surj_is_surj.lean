import functions

theorem surj_surj_is_surj { S T U : Type } { f : S → T } { g : T → U }
( hf : surjective f ) ( hg : surjective g )
: surjective ( g ∘ f ) := by
  intro u
  cases hg u with
  | intro t ht =>
    cases hf t with
    | intro s hs =>
      exact ⟨s, show g (f s) = u by rw [hs, ht]⟩
