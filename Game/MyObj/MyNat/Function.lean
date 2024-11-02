-- from NNG4
-- ちょっと編集済み
import Game.MyObj.MyNat.MyNat

namespace MyGame

opaque add : MyNat → MyNat → MyNat

instance instAdd : Add MyNat where
  add := MyGame.add

axiom add_zero (a : MyNat) : a + 0 = a

axiom add_succ (a d : MyNat) : a + d′ = (a + d)′

theorem ofNat_succ : (OfNat.ofNat n′ : ℕ) = (OfNat.ofNat n)′ := _root_.rfl

opaque mul : MyNat → MyNat → MyNat

instance : Mul MyNat where mul := MyGame.mul

axiom mul_zero (a : MyNat) : a * 0 = 0

axiom mul_succ (a b : MyNat) : a * b′ = a * b + a

opaque pow : ℕ → ℕ → ℕ

-- notation `a ^ b` for `pow a b`
instance : Pow ℕ ℕ where
  pow := pow

-- Note: since v4.2.0-rc2
macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : MyNat) ($y : MyNat))

axiom pow_zero (m : ℕ) : m ^ 0 = 1

axiom pow_succ (m n : ℕ) : m ^ n′ = m ^ n * m
