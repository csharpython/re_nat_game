import Game.Metadata
import Game.Levels.Tutorial

World "Addition"
Level 1

Title "数学的ドミノ倒し(Zero_add)"

namespace MyGame
/--
## 説明
数学的帰納法を使うために必要なタクティクです。

## 構文
`induction X` Xについての帰納法を行います。
`induction X with Y Z` Xについての帰納法を新たな変数Y、仮定Zを使って行います。
-/
TacticDoc induction

Introduction "
## あらかじめ言っておきます。
**このゲームで和の定義として使われているのは
$a+0=a$と$a + b′=(a + b)′$のみです。
$0+a=a$は定義として使われていません。**

## 数学的帰納法
A. $n = 0$の時、P。
B. $n = k$の時にPなら、$n = k′$の時もP。
この2つが成り立つなら、nがどんな自然数であってもP。
このことを使う証明を、数学的帰納法といいます。
**自然数がかかわる問題では、かなり使いやすいです!**
"

/--
## 説明
$x$を自然数とする。$0+x=x$である。
-/
TheoremDoc MyGame.zero_add as "zero_add" in "+"

/--$∀x∈ℕ,0 + x = x$-/
Statement zero_add {x:ℕ} : 0 + x = x := by
  Hint "`induction x`"
  induction x
  rewrite[add_zero]
  rfl
  rewrite[add_succ,n_ih]
  rfl

Conclusion "
いいですね！数学的帰納法を使って、いろいろなことを証明してみましょう！
"

/- Use these commands to add items to the game's inventory. -/

NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
