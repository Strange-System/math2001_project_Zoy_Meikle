import functions

theorem surj_surj_is_surj { S T U : Type } { f : S → T } { g : T → U }
( hf : surjective f ) ( hg : surjective g )
: surjective ( g ∘ f ) := by
  unfold surjective
  unfold surjective at hf
  unfold surjective at hg
  intro x
  cases hg x with
  | intro y hy =>
      change ∃ z, g (f z) = x
      cases hf y with
      | intro z hz =>
          apply Exists.intro z
          rewrite [hz]
          exact hy
