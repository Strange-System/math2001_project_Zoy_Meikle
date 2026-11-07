import functions
import natural_numbers

def floordiv : ℕ → ℕ → ℕ
| 0, _ => 0
| ℕ.succ n, m =>
  let r := (remainder n m).succ
  if r = m then (floordiv n m).succ else (floordiv n m)

def natsubtract : ℕ → ℕ → ℕ
| 0, _ => 0
| ℕ.succ n, ℕ.succ m => natsubtract n m
| ℕ.succ n, ℕ.zero => n.succ

infixl:65 " ∸ " => natsubtract
infixl:70 " ÷ " => floordiv
