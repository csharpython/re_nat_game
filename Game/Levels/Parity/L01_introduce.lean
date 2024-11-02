import Game.Levels.Mul
import Game.Levels.Le
import Game.MyObj.MyNat.Parity

World "Parity"
Level 1

Title "偶奇"

namespace MyGame

Introduction "
偶数、奇数について考えましょう！
"

TheoremTab "2n"

/--
## 説明
0は偶数
-/
TheoremDoc MyGame.zero_is_even as "zero_is_even" in "2n"
/--
  自然数が偶数か判定する
  `even n ↔ ∃ (m : ℕ), m * 2 = n`
-/
DefinitionDoc MyGame.even as "even"


/--0 is even-/
Statement zero_is_even : even 0 := by
  Hint(hidden := true) "`exists`"
  exists 0
  rewrite[zero_mul]
  rfl
Conclusion "
0は偶数ですね！
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
