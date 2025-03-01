import Game.Levels.MulEX.L02_mul_le_mul_right

World "MulEX"
Level 3

Title "複製(le_mul_right)"

namespace MyGame

Introduction "
2倍！3倍！
"

TheoremTab "*"

/--
## 説明
$a,b$を自然数とする。$a≤a \times b′$である。
-/
TheoremDoc MyGame.le_mul_right as "le_mul_right" in "*"

/--$∀(a,b)∈ℕ^2 , a≤a \times b′$-/
Statement le_mul_right (a b:ℕ) : a  ≤ a * b′ := by
  Hint(hidden := true) "`cases`でどうぞ"
  exists a * b
  rewrite[add_comm]
  apply mul_succ
Conclusion "
なんか`cases`の役割多くない？
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
