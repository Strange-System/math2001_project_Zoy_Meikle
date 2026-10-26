import natural_numbers
import ne_succ

theorem lt_succ (n : ℕ)
: n < n.succ := by
  unfold lt
  unfold le
  constructor
  ·
    apply Exists.intro ℕ.zero.succ
    rfl
  ·
    apply ne_succ
