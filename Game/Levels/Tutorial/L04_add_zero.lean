import Game.Metadata
import Game.MyObj.MyNat.Function

World "Tutorial"
Level 4

Title "Thm."

namespace MyGame
Introduction"
# 定理の使用
Leanで使えるのは、仮定だけではありません。
すでに分かっていること「定理」も使えます！

## 0は自然数か問題
このゲームでは、$0$は自然数であるとします。
そうした方が(このゲームでは)都合がいいからです。
"
TheoremTab "+"

/--
  自然数の加算。
  add_zero `a + 0 = a` と、
  add_succ `a + b′ = (a + b)′`
  で定義される。
-/
DefinitionDoc MyGame.add as "+"

/--
  $a′ = aの次$
  直接入力するなら`\prime`を使おう！
-/
DefinitionDoc MyGame.MyNat.succ as "′"

NewDefinition MyGame.add MyGame.MyNat.succ

/--
## 説明
`repeat tactic`とすることで、`tactic`を失敗するまで繰り返します。
-/
TacticDoc «repeat»

NewHiddenTactic «repeat»

/--
## 説明
aを自然数とする。a+0=aである。
-/
TheoremDoc MyGame.add_zero as "add_zero" in "+"

NewTheorem MyGame.add_zero

/--$∀\{a,b,c\}∈ℕ^3,a + (b + 0) + (c + 0) = a + b + c$-/
Statement (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  Hint "`rewrite[add_zero]`で`b+0`が`b`になります。"
  rewrite[add_zero,add_zero]
  rfl

Conclusion "実は、`repeat (Tactic)`を使うと、
Tacticを失敗するまで繰り返してくれます。便利ですね
"
