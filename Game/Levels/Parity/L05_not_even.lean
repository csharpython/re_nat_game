import Game.Levels.Parity.L04_not_odd

World "Parity"
Level 5

Title "¬偶↔奇"

namespace MyGame

Introduction "
もう一度やってみましょう
"

TheoremTab "2n"

/--
## 説明
偶数でない自然数は奇数
-/
TheoremDoc MyGame.not_even as "not_even" in "2n"


/--$∀n∈ℕ,¬\operatorname{even} n↔\operatorname{odd} n$-/
Statement not_even(n:ℕ) : ¬even n↔odd n := by
  constructor <;> intro
  cases odd_or_even n
  exact False.elim (a h)
  exact h
  intro b
  exact odd_nand_even n ⟨b,a⟩
Conclusion "
これもよく使う補題です。
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic obtain
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
