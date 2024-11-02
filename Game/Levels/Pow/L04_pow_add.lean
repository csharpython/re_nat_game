import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Mul

World "Power"
Level 4

Title "対数(pow_add)"

namespace MyGame

Introduction "
対数って、大きな数を表すとき便利ですよね。
実は身近なところでも使われています(?)。
「浮動小数点型」で調べてみるといいですよ。
"
TheoremTab "^"

/--
## 説明
$x$を自然数とする。$x^{a+b}=x^a x^b$である。
-/
TheoremDoc MyGame.pow_add as "pow_add" in "^"

/--$∀\{x,a,b\}∈ℕ³→x^{a+b}=x^a x^b$-/
Statement pow_add (x a b:ℕ) : x ^ (a + b) = x ^ a * x ^ b := by
  Hint(hidden := true) "まあ、`induction b`ですね。"
  induction b
  rewrite[pow_zero,add_zero,mul_one]
  rfl
  rewrite[add_succ,pow_succ,pow_succ,n_ih,mul_assoc]
  rfl

Conclusion "私は競プロ勢なので、double型はあまり使いません　by 作者"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
