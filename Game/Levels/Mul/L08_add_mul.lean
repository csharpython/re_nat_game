import Game.Metadata
import Game.Levels.Mul.L04_mul_comm
import Game.Levels.Mul.L07_mul_add

World "Multiplication"
Level 8

Title "分散 Ⅱ (add_mul)"

namespace MyGame

Introduction "
頑張ってください！
"

TheoremTab "*"

/--
## 説明
$a,b,c$を自然数とする。$(a+b)c=ac+bc$である。
-/
TheoremDoc MyGame.add_mul as "add_mul" in "*"

/--$∀\{a,b,c\}∈ℕ³,a(b+c) = ab + ac$-/
Statement add_mul (a b c:ℕ) : (a + b) * c = a * c + b * c := by
  Hint (hidden := true) "`rewrite[mul_comm]`"
  rewrite[mul_comm,mul_add]
  repeat rewrite[mul_comm c]
  rfl
Conclusion "
さあ、`mul_assoc`に挑もう...!
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
