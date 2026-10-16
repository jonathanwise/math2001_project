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


def le ( m n : ℕ ) : Prop :=
  ∃ (k:ℕ), k + m = n

def lt ( m n : ℕ ) : Prop :=
  ( le m n ) ∧ ¬ ( m = n )

macro_rules
| `($m ≤ $n) => `(le $m $n)
| `($m < $n) => `(lt $m $n)
| `($m ≥ $n) => `(le $n $m)
| `($m > $n) => `(lt $n $m)

@[app_unexpander le]
meta def unexpandLe : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ≤ $b)
  | _ => throw ()

@[app_unexpander lt]
meta def unexpandLt : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a < $b)
  | _ => throw ()


/- This definition should be equivalent to
Definition 0.36 of the textbook.  Note: 
divides m n should mean that m divides n,
or, equivalently, that n is a multiple of n
by a natural number. -/

def divides (m n : ℕ) : Prop :=
  ∃ (k:ℕ), k*m = n
