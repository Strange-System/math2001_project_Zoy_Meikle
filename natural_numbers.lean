inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ


namespace ℕ
protected def ofNat : Nat → ℕ
  | 0          => .zero
  | Nat.succ n => .succ (ℕ.ofNat n)

@[default_instance 200]
instance (n : Nat) : OfNat ℕ n where
  ofNat := ℕ.ofNat n
end ℕ


def plus : ℕ → ℕ → ℕ
  | ℕ.zero, n => n
  | ℕ.succ m, n => ℕ.succ ( plus m n )

def times : ℕ → ℕ → ℕ
  | ℕ.zero, _ => ℕ.zero
  | ℕ.succ m, n => plus n ( times m n )

def divisible : ℕ → ℕ → Prop
  | ℕ.zero, ℕ.zero => False
  | m, n => ∃ k : ℕ, times k n = m

macro_rules
| `($m + $n) => `(plus $m $n)
| `($m * $n) => `(times $m $n)

@[app_unexpander plus]
meta def unexpandPlus : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a + $b)
  | _ => throw ()

@[app_unexpander times]
meta def unexpandTimes : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a * $b)
  | _ => throw ()

#reduce (types := true) divisible 0 0

example : divisible 4 2 := by
  exact ⟨2, rfl⟩
