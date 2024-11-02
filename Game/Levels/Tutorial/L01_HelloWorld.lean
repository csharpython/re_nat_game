import Game.Metadata
import Game.MyObj.MyNat.Function

World "Tutorial"
Level 1

Title "はじめの一歩"

namespace MyGame
/--
## 説明
`X=X`といった形のゴールを閉じます。
これは、**定義として**等しい場合のみ有効です。
ただ、このゲームでは関数の値は「公理」として実装されていることが多いので、
基本的には左辺と右辺が**完全に**一致する場合のみ有効だと思います。
(ちなみに、公理は数学の前提的なもの)
-/
TacticDoc rfl

Introduction "
# 最初に読むこと。
ここには役立つ情報がたくさん書いてあるはずです。

このゲームでやるべきことはシンプル。
ゴールとして存在する式を証明することです。
...どうやるのかって？「タクティク」を使い、ゴールを変形したり、閉じたりします。

## 新しいタクティク：`rfl`
このタクティクは$X = X$の形のゴールを閉じます。
このステージのゴールに使えそうですね！
"

/--$x$と$y$が自然数なら、$33 * x + 24 * y = 33 * x + 24 * y$である。-/
Statement (x y:ℕ) : 33 * x + 24 * y = 33 * x + 24 * y := by
  Hint "左辺と右辺が同じ時は、rflを使うとゴールを閉じれます。"
  rfl

Conclusion "「$33 * x + 24 * y = 33 * x + 24 * y$である。だから$33 * x + 24 * y = 33 * x + 24 * y$なのだ。」
では済まない命題も結構あるのですが...まあそれの示し方は次のステージで話しましょう。
"

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
