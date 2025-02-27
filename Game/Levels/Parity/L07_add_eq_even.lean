import Game.Levels.Parity.L04_not_odd
import Game.Levels.Parity.L05_not_even
World "Parity"
Level 7

Title "偶+奇"

namespace MyGame

Introduction "
奇数+奇数=偶数
"

TheoremTab "2n"

/--
## 説明
偶数となにかの和が偶数なら両方偶数
-/
TheoremDoc MyGame.add_eq_even as "add_eq_even" in "2n"

/--$偶数となにかの和が偶数なら両方偶数$-/
Statement add_eq_even(n m:ℕ) : even (n+m)↔(even n ↔ even m) := by
  have sym1 (x y:ℕ)(h: even (x+y))(i:even x) : even y := by
    cases h
    cases i
    cases h
    cases le_total w_1 w <;> cases h <;> cases h_2 <;> rewrite[add_mul] at h_1
    apply add_left_cancel at h_1
    exists w_2
    rewrite[succ_mul,eq_comm,add_assoc,add_assoc] at h_1
    apply add_right_eq_self at h_1
    rewrite[two_eq_succ_one,succ_add,eq_comm] at h_1
    exact False.elim (zero_ne_succ _ h_1)
  constructor <;> intro
  constructor <;> intro
  exact sym1 n m a a_1
  rewrite[add_comm] at a
  exact sym1 m n a a_1
  cases odd_or_even n
  have i := h
  rewrite[a] at h
  cases i
  cases h_1
  cases h
  cases h_1
  rewrite[←add_mul]
  exists w + w_1
  cases odd_or_even m
  rewrite[←a] at h_1
  exact False.elim (odd_nand_even n ⟨h_1,h⟩)
  cases h
  cases h_2
  cases h_1
  cases h
  rewrite[add_right_comm,←add_assoc,←add_mul,add_assoc,←mul_two,←add_mul]
  exists w+w_1+1
Conclusion "
ポチ
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic constructor
--NewTheorem NewTheorem eq_comm
-- NewDefinition Nat Add Eq
