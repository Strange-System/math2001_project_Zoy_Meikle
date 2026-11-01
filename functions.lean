def injective {S T : Type} (f : S → T)
: Prop
:= ∀ (x y : S), f x = f y → x = y

def surjective {S T : Type} (f : S → T)
: Prop
:= ∀ (x : T), ∃ (y : S), f y = x

def composition {S T U : Type} (g : T → U) (f : S → T) 
: S → U 
:= fun x => g ( f x )

macro_rules 
| `($g ∘ $f) => `(composition $g $f)

@[app_unexpander composition]
meta def unexpandComposition : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ∘ $b)
  | _ => throw ()
