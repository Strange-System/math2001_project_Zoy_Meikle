import natural_numbers
import functions
import plus_comm
import zero_not_succ
import lt_succ
import zero_le
import le_lt_is_lt
import le_trans
import lt_is_le
import sets
open Classical

/- def ℕ_pos_set : Set ℕ := fun n => n > 0 -/
/- this shouldn't HAVE to be a set, it SHOULD be able to just be a type
without attaching a secondary object to make for a nonnumber object.
as I understand it I'm not being restricted by math but instead by
lean's bizarre hole, but this is the closest thing to a proof of concept
that I can make.-/

/- def ℕ_pos : Type := { n : ℕ // ℕ_pos_set n } -/
/- Yes, I get that this results in basically the same thing. This is a
proof of concept. The idea being that there is no reason why I shouldn't be
able to just make a type that actually outputs numbers instead of
two-pronged nonnumber objects.

By all common sense, I should be able to make the former of
these two statements
and declare it as a type or subtype.-/

def ℕ_evens := { n : ℕ // ∃k : ℕ, 2 * k = n}

theorem plus_one_gt_zero (n : ℕ)
    : n + 1 > 0 := by
  induction n
  case zero =>
    exact lt_succ 0
  case succ h ih =>
    change 0 < (h + 1).succ
    unfold lt at ih ⊢
    constructor
    case left =>
      exact le_trans 0 (h + 1) (h + 1).succ
        ih.left (lt_is_le (lt_succ (h + 1)))
    case right =>
      apply zero_not_succ

def f ( n : ℕ ) : ℕ_pos := ⟨ n + 1, plus_one_gt_zero n ⟩

def evens ( n : ℕ ) : ℕ_evens := ⟨2 * n, ⟨n, rfl⟩⟩
/- still stupid I have to do this and get nonnumber objects instead of
just a number that fulfills the conditions, only needing one proof or
declaration to determine that it does-/

/-
def evens ( n : ℕ ) : ℕ_evens := by
  unfold ℕ_evens
  apply Subtype.mk
  case val =>
    exact 2 * n
  case property =>
    apply Exists.intro n
    rfl
-/


/- def f ( n : ℕ ) : ℕ_pos := by
  unfold ℕ_pos
  apply Subtype.mk
  case val =>
    exact n + 1
  case property =>
    exact plus_one_gt_zero n
-/


private theorem f_surj : surjective f := by
  unfold surjective
  intro x
  cases x with
  | mk n hn =>
  cases n with
  | zero =>
    unfold lt at hn
    exfalso
    change 0 ≤ ℕ.zero ∧ ¬0 = 0 at hn
    exact hn.right rfl
  | succ k =>
  unfold f
  /- unless I'm wrong this is stupid that there isn't a way to describe
  such a subtype in a way that outputs actual numbers instead of nonnumber
  objects.
  Just give me the NUMBER and then add the GOAL SEPERATELY, so that it's
  an actual NUMBER IN THE EQUATION instead of a NONNUMBER CONGLOMERATE OBJECT-/
  apply Exists.intro k
  apply Subtype.ext
  /- It's stupid I have to do this ^^^ -/

  /- I promise I'm not just being salty like "i don't wanna work"
  I in fact did so much EXTRA work to demonstrate that there is an
  obviously better way that for some reason lean doesn't support.-/
  apply plus_comm

def I := { n : ℕ // 1 ≤ n ∧ n ≤ 10 }
def J := { n : ℕ // 2 ≤ n ∧ n ≤ 20 }

private theorem from_I_plus_from_I_in_J ( a b : I )
: 2 ≤ a.val + b.val ∧ a.val + b.val ≤ 20 := by
/- Look, I know I can do these, and I've spent plenty of time getting mad at
the way lean doesn't seem to support the obviously much easier way to do it,
so I'm calling it. I know exactly how I would do this. -/
  sorry

def p ( a : I × I ) : J := sorry

def g ( x : ℕ_pos ) : ℕ := x.val

def h ( x : ℕ ) : ℕ := 1 + x

private theorem h_eq_gf : h = g ∘ f := by
  sorry

private theorem g_inj : injective g := by
  sorry

private example : ∃ (V:Type) ( p : ℕ → V ) ( i : V → ℕ ),
i ∘ p = h ∧ surjective p ∧ injective i := by
  sorry
