import Game.Metadata
import Game.Levels.Pow.L04_pow_add

World "Power"
Level 5

Title "上底(mul_pow)"

namespace MyGame

Introduction "
Try it!
"
TheoremTab "^"

/--
## 説明
$x$を自然数とする。$(ab)^x=a^x b^x$である。
-/
TheoremDoc MyGame.mul_pow as "mul_pow" in "^"

/--$∀\{x,a,b\}∈ℕ³→(ab)^x=a^x b^x$-/
Statement mul_pow (x a b:ℕ) : (a * b) ^ x = a ^ x * b ^ x := by
  induction x
  rewrite[pow_zero,pow_zero,pow_zero,mul_one]
  rfl
  Hint "`mul_comm`を使うとき、その後ろに何かしらを指定する必要があります。"
  rewrite[pow_succ,pow_succ,pow_succ,n_ih,mul_assoc]
  repeat rewrite[mul_comm (b^n)]
  repeat rewrite[←mul_assoc]
  rfl

Conclusion "Nice try!"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
