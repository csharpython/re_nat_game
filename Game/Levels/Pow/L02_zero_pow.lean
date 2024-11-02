import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Mul

World "Power"
Level 2

Title "Re:虚無(zero_pow)"

namespace MyGame

Introduction "
## Leanに確認してもらおう！
「うまく行ってると思っていたら、途中でミスに気づいて全部やり直し」
みたいなこと、よくありますよね?
Leanでは、証明が正しいことのチェックを自動的に行ってくれます！
...あれ？何か既視感がある...
"
TheoremTab "^"

/--
## 説明
$x$を自然数とする。$0^{x′} = 0$である。
-/
TheoremDoc MyGame.zero_pow as "zero_pow" in "^"

/--$∀x∈ℕ,0^{x′}=0$-/
Statement zero_pow (x:ℕ) : 0 ^ x′ = 0 := by
  rewrite[pow_succ,mul_zero]
  rfl

Conclusion "ちなみに、$0^0=1$です。このゲームの中では..."

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
