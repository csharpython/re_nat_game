-- from NNG4
-- ちょっと編集した
/-- Our copy of the natural numbers called `MyNat`, with notation `ℕ`. -/
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat
-- deriving BEq, DecidableEq, Inhabited

@[inherit_doc]
notation (name := MyNatNotation) (priority := 1000000) "ℕ" => MyNat
-- Note: as long as we do not import `Mathlib.Init.Data.Nat.Notation` this is fine.
notation:300 a:300 "′" => MyNat.succ a
-- Note: This was originally ‘ (\lq) but I thought ′ (\prime) is better.
-- I have a question. What is ‘?

namespace MyGame

instance : Inhabited MyNat where
  default := MyNat.zero

def ofNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero   => MyNat.zero
  | Nat.succ b => (ofNat b)′

def toNat (x : MyNat) : Nat :=
  match x with
  | MyNat.zero   => 0
  | b′ => Nat.succ (toNat b)

instance instofNat {n : Nat} : OfNat MyNat n where
  ofNat := ofNat n

instance : ToString MyNat where
  toString p := toString (toNat p)

theorem zero_eq_0 : MyNat.zero = 0 := rfl

def one : MyNat := 0′

theorem succ_inj (x y:MyNat) : x′ = y′ → x = y := MyNat.succ.inj
theorem zero_ne_succ (x:MyNat) : 0 = x′ → False := MyNat.noConfusion
