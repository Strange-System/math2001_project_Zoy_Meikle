import functions

theorem inj_inj_is_inj { S T U : Type } { f : S → T } { g : T → U }
( hf : injective f ) ( hg : injective g )
: injective ( g ∘ f ) := by
  unfold injective
  intro x y h
  change g (f x) = g (f y) at h
  have h1 : (f x) = (f y) := by
    unfold injective at hg
    apply hg
    exact h
  unfold injective at hf
  apply hf
  exact h1
