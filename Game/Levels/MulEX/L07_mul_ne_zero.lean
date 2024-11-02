import Game.Levels.MulEX.L01_mul_eq_zero

World "MulEX"
Level 7

Title "対偶(mul_ne_zero)"

namespace MyGame

Introduction "
**`rewrite`、`rfl`無効**
対偶とは何でしょうか？
"
/--
## 説明
`contrapose! h`とすると、ゴールと仮定`h`が入れ替わり、さらに両方が否定されます。
対偶ですね
-/
TacticDoc contrapose

TheoremTab "*"

/--
## 説明
$a,b$を自然数とする。$a≠0$かつ$b≠0$なら$ab≠0$である。
-/
TheoremDoc MyGame.mul_ne_zero as "mul_ne_zero" in "*"

DisabledTactic rewrite rfl
/--$∀\{a,b\}∈ℕ²,(a≠0∧b≠0)→ab≠0$-/
Statement mul_ne_zero (a b:ℕ)(h:a≠0∧b≠0) : a*b≠0:= by
  contrapose! h
  intro i
  cases mul_eq_zero a b h with h h
  exact False.elim (i h)
  exact h
Conclusion "
なぜ簡単な問題が2連続で出たのでしょう？
しかもこれEXTRAだし。
「嵐の前の静けさ」ですかね。
"

/- Use these commands to add items to the game's inventory. -/

NewTactic contrapose
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
