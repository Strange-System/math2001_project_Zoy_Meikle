import functions

theorem id_bijection { S : Type }
: ( bijective ( id : S → S ) ) := by
  unfold bijective
  apply And.intro
  case left =>
    unfold injective
    intro x y
    intro h
    unfold id at h
    exact h
  case right =>
    unfold surjective
    intro x
    unfold id
    apply Exists.intro x
    rfl
