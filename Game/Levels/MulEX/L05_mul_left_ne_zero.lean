import Game.Levels.Mul
import Game.Levels.Le

World "MulEX"
Level 5

Title "因数分解・裏(mul_left_ne_zero)"

namespace MyGame

/--
## 説明
`P→Q`のようなゴールに対して`intro h`とすると、
仮定`h:P`が追加され、ゴールが`Q`になります。
また、`∀(a:ℕ),P a`にたいして`intro n`とすると、
仮定に`n:ℕ`が追加され、ゴールが`P n`になります。

## 補足
一部、`intro`が使えなさそうでも使える場合があります。
例
`N≠M`:これは`(N=M)→False`の略記です。
`¬P`:これは`P→False`の略記です。
-/
TacticDoc intro

Introduction "
## 新しいタクティク：`intro`
\"PならばQ\"といった形のゴールに対して使えます。

$p→q$に対する裏：$¬p→¬q$
"

TheoremTab "*"

/--
  `a≠b`は`a=b→False`の略記。
  直接入力するなら`\ne`を使おう！
-/
DefinitionDoc Ne as "≠"

/--
## 説明
$a,b$を自然数とする。$ab≠0$なら$b≠0$である。
-/
TheoremDoc MyGame.mul_left_ne_zero as "mul_left_ne_zero" in "*"

/--$∀\{a,b\}∈ℕ²,ab≠0→b≠0$-/
Statement mul_left_ne_zero (a b:ℕ)(h:a*b≠0) : b≠0 := by
  Hint "`intro`でどうぞ。"
  intro i
  rewrite[i,mul_zero] at h
  Hint "ここで`0≠0`は`(0=0)→False`の略記であることを思い出しましょう"
  apply h
  rfl
Conclusion "
とうとう`cases`以外にも光が...！
"

/- Use these commands to add items to the game's inventory. -/

NewTactic intro
-- NewTheorem eq_comm
NewDefinition Ne
