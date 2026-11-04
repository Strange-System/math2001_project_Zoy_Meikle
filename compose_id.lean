import functions

theorem compose_id { f : S → T }
: f ∘ id = f := by
  funext x
  unfold compose
  unfold id
  rfl
