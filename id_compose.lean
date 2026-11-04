import functions

theorem id_compose { f : S → T }
: id ∘ f = f := by
  funext x
  unfold compose
  unfold id
  rfl
