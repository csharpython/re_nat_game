import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Add

World "Multiplication"
Level 2

Title "虚無(zero_mul)"

namespace MyGame

Introduction "
## Leanに確認してもらおう！
「うまく行ってると思っていたら、途中でミスに気づいて全部やり直し」
みたいなこと、よくありますよね?
Leanでは、証明が正しいことのチェックを自動的に行ってくれます！
"

TheoremTab "*"

/--
## 説明
$x$を自然数とする。$0*x=0$である。
-/
TheoremDoc MyGame.zero_mul as "zero_mul" in "*"

/--$∀n∈ℕ,0 × n = 0$-/
Statement zero_mul (n:ℕ) : 0 * n = 0 := by
  induction n
  exact mul_zero 0
  rewrite[mul_succ,n_ih,add_zero]
  rfl
Conclusion "
掛け算も、意外と簡単ですね。
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
