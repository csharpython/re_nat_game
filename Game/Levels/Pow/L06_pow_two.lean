import Game.Metadata
import Game.Levels.Pow.L01_pow_one

World "Power"
Level 6

Title "四角(mul_pow)"

namespace MyGame

Introduction "
理解していればできるはずです。
"
TheoremTab "^"

/--
## 説明
$x$を自然数とする。$x ^ 2= xx$である。
-/
TheoremDoc MyGame.pow_two as "pow_two" in "^"

/--$∀x∈ℕ,x^2=xx$-/
Statement pow_two (x:ℕ) : x^2 = x * x:= by
  rewrite[two_eq_succ_one,pow_succ,pow_one]
  rfl

Conclusion "Nice try!"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
