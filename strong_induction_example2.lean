import natural_numbers
import strong_induction
import fibonacci
import remainders_by_3
import odd_iff_not_even
import even_plus_odd_is_odd
import odd_plus_odd_is_even
import odd_plus_even_is_odd
import lt_succ
import lt_is_le


local notation "F" => Fibonacci

private theorem trichotomy ( n : ℕ )
: ( n = 0 ) ∨ ( n = 1 ) ∨ ( ∃ (m:ℕ), n = m.succ.succ )
:= by
  sorry



example ( n : ℕ )
: ( n % 3 ) = 0 ↔ ( F n % 2 ) = 0
:= by
  induction n using strong_induction
  case ih n ih =>
  rcases trichotomy n with h|h|h
  /-rcases does cases recursively
  on the whole thing, otherwise
  we would have to do cases on the
  first and second ∨ -/
  · -- n = 0
    /- · is just to help organize
    and only focus on one case at a time-/
    rewrite [h]
    decide

    sorry
  · -- n =1
    rewrite [h]
    decide
    sorry
  · -- n = m + 2
    sorry
