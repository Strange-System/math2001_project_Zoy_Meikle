import functions
import natural_numbers

def pseudodivision : ℕ → ℕ → ℕ
| 0, _ => 0
| n, m : ∃ (k:ℕ), k*m = n =>
  k
| n, m : ¬(∃ (k:ℕ), k*m = n) =>
