import Game.Levels.Add.L03_Add_comm
import Game.Levels.Add.L06_add_right_cancel

World "Addition"
Level 7

Title "↔"

/--
## 説明
ゴールと同じ仮定`t`があるとき、`exact t`でゴールを閉じることができます。
-/
TacticDoc exact

namespace MyGame
Introduction "
**警告：このレベルでは`rfl`が無効です。**

## 新しいタクティク:`exact`
`rfl`とはまた違ったゴールの閉じ方を紹介します。
これは、ゴールと同じ仮定があるときに使えるものです。
`exact` では、$P$ならば$P$であるということを使えます！
早速使っていきましょう！
"

/--
## 説明
$x,y,z$を自然数とする。$n+x=n+y$なら$x=y$である。
-/
TheoremDoc MyGame.add_left_cancel as "add_left_cancel" in "+"

DisabledTactic rfl
/--$∀\{x,y,n\}∈ℕ^3,n + x = n + y → x = y$-/
Statement add_left_cancel (x y n:ℕ)(h:n + x = n + y) : x = y := by
  rewrite[add_comm] at h
  Hint (hidden := true)(strict := true) "
ここでただ`rewrite[add_comm] at h`を行うと、`x + n`が元に戻るだけです。
変数を指定して、`y + n`を交換できるようにしましょう。
やり方？W+-5を思い出して！"
  rewrite[add_comm n] at h
  Hint (hidden := true)(strict := true) "
ここでただ`exact add_right_cancel`とするだけでは、(案の定)うまく行きません。
どうやら今回も、変数**と仮定**を指定する必要がありそうです...
"
  exact add_right_cancel x y n h

Conclusion "
もう一つのゴールの閉じ方はわかりましたか？
"

NewTactic exact
/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
