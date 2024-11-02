import Game.Levels.Parity.L01_introduce

World "Parity"
Level 3

Title "偶奇-3"

namespace MyGame

Introduction "
自然数は偶数と奇数の
ど　ち　ら　か　一　方です。
"

TheoremTab "2n"


/--
## 説明
$a=b$なら$b=a$
-/
TheoremDoc eq_comm as "eq_comm" in "Prop"
/--
## 説明
自然数が(偶数かつ奇数)にならない
-/
TheoremDoc MyGame.odd_nand_even as "odd_nand_even" in "2n"


/--$∀n∈ℕ,even n∨odd n$-/
Statement odd_nand_even(n:ℕ) : ¬(even n ∧ odd n) := by
  intro h
  cases h with l r
  induction n with n hn
  cases r with e r
  rewrite[add_one_eq_succ,eq_comm] at r
  exact zero_ne_succ _ r
  cases l with m l
  cases r with x r
  rewrite[add_one_eq_succ] at r
  apply hn
  exists x
  exact succ_inj _ n r
  cases m
  rewrite[zero_mul] at l
  exact False.elim (zero_ne_succ n l)
  exists a
  rewrite[succ_mul,two_eq_succ_one,add_succ,←two_eq_succ_one] at l
  exact succ_inj _ _ l
Conclusion "
Q.何でこんな難しいんですか?

A.私も同意見です
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic obtain
NewTheorem NewTheorem eq_comm
-- NewDefinition Nat Add Eq
