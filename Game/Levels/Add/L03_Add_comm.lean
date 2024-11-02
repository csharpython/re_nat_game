import Game.Metadata
import Game.Levels.Add.L02_succ_add

World "Addition"
Level 3

Title "Boss:Sym.(add_comm)"

namespace MyGame

Introduction "
[それっぽい音楽]

交換法則を証明しましょう！頑張ってください！
※先ほど証明した`succ_add`を活用しましょう！
"

/--
## 説明
$x,y$を自然数とする。$x+y=y+x$である。
-/
TheoremDoc MyGame.add_comm as "add_comm" in "+"

/--$∀\{x,y\}∈ℕ^2,x + y = y + x$-/
Statement add_comm (x y:ℕ) : x + y = y + x := by
  Hint "どちらを選んでもいいです。とりあえずxについて帰納法しましょうか。"
  induction x
  rewrite[add_zero,zero_add]
  rfl
  Hint(hidden := true)(strict := true) "{n_ih} が使えるように、式を変形してみましょう。`succ_add`が使えるはずです。"
  rewrite[succ_add,add_succ,n_ih]
  rfl
Conclusion "
お疲れさまでした！このように、整数絡みの問題では帰納法が役立つことが多いです！
覚えておきましょう！
"

/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
