import Game.Levels.Mul
import Game.Levels.Le

World "MulEX"
Level 2

Title "大小関係(mul_le_mul_right)"

namespace MyGame

Introduction "
これは≤タブと*タブのどちらに入れるべきでしょうか...
"

TheoremTab "*"

/--
## 説明
$a,b,m$を自然数とする。$a≤b$なら$a\*m≤b\*m$である。
-/
TheoremDoc MyGame.mul_le_mul_right as "mul_le_mul_right" in "*"

/--$∀\{a,b,m\}∈ℕ³ ,a ≤ b → am≤bm$-/
Statement mul_le_mul_right (a b m:ℕ)(h : a ≤ b) : a * m ≤ b * m := by
  Hint(hidden := true) "`cases`でどうぞ"
  cases h
  exists w*m
  rewrite[h_1]
  apply add_mul
Conclusion "
あなたはどうおもいます？
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
