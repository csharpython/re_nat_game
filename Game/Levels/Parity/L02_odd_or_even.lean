import Game.Levels.Parity.L01_introduce

World "Parity"
Level 2

Title "偶奇-2"

namespace MyGame

Introduction "
偶数か奇数です。全ての数は
"

TheoremTab "2n"

/--
## 説明
自然数は偶数か奇数
-/
TheoremDoc MyGame.odd_or_even as "odd_or_even" in "2n"
/--
  自然数が奇数か判定する
  `odd n ↔ ∃ (m : ℕ), m*2+1 = n`
-/
DefinitionDoc MyGame.odd as "odd"


/--$∀n∈ℕ,even n∨odd n$-/
Statement odd_or_even(n:ℕ) : even n ∨ odd n := by
  Hint(hidden := true) "`induction`"
  induction n with n hn
  exact Or.inl zero_is_even
  cases hn
  cases h with w h
  apply Or.inr
  exists w
  rewrite[h,add_one_eq_succ]
  rfl
  cases h with w h
  apply Or.inl
  exists w+1
  rewrite[add_mul,one_mul,←h,←add_succ,two_eq_succ_one]
  rfl
Conclusion "
自然数は偶数か奇数
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
