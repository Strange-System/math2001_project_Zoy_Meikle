import natural_numbers
import peano

theorem ne_succ ( n : ℕ )
: n ≠ n.succ := by
  unfold Ne
  induction n
  case zero =>
    decide
  case succ n ih =>
    intro h
    injection h with h'
    contradiction
