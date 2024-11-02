import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Mul

World "Power"
Level 3

Title "Re:不変(one_pow)"

namespace MyGame

Introduction "
掛け算と要領は変わらないはずです。頑張れ！
"
TheoremTab "^"

/--
## 説明
$x$を自然数とする。$1^x=1$である。
-/
TheoremDoc MyGame.one_pow as "one_pow" in "^"

/--$∀x∈ℕ,1^x=1$-/
Statement one_pow (x:ℕ) : 1 ^ x = 1 := by
  induction x
  exact pow_zero 1
  rewrite[pow_succ,mul_one]
  exact n_ih

Conclusion "普段と変わらない日常も好きです。by 作者"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
