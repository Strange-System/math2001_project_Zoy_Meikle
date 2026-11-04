import functions

theorem comp_surj_then_second_surj { S T U : Type } { f : S → T } { g : T → U }
( h : surjective ( g ∘ f ) )
: surjective g := by
  unfold surjective at h
  unfold surjective
  unfold compose at h
  intro u
  have h1 := h u
  cases h1 with
  | intro s gfs =>
    apply Exists.intro (f s)
    exact gfs
