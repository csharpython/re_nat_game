import Game.Metadata
import Game.Levels.Add.L01_zero_add

World "Addition"
Level 2

Title "Lem."

namespace MyGame

Introduction "
これは交換法則を証明するのに必要な奴です。
頑張ってください。
え、何でこれが必要なのかって？まあ、やってみればわかりますよ...
"

/--
## 説明
$x y$を自然数とする。$x′+y=(x+y)′$である。
-/
TheoremDoc MyGame.succ_add as "succ_add" in "+"

/--$∀\{x,y\}∈ℕ^2,x′ + y = (x + y)′$-/
Statement succ_add (x y:ℕ) : x′ + y = (x + y)′ := by
  Hint (hidden := true)"`induction y`"
  induction y
  rewrite[add_zero,add_zero]
  rfl
  rewrite[add_succ,add_succ,n_ih]
  rfl
Conclusion "
いいですね！
"

/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
