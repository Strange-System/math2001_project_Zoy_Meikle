import natural_numbers

/- These definitions should follow
Definition 0.41 from the textbook. -/


def is_even ( n : ℕ ) : Prop :=
  divides 2 n

def is_odd ( n : ℕ ) : Prop :=
  ¬is_even n
