import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Mul

World "Power"
Level 1

Title "Re:等倍(pow_one)"

namespace MyGame

Introduction "
累乗のチュートリアルです。
累乗は、$n^0=1$と$m^{n′}=m^nm$の2つで定義されます。
掛け算の時と似ていますね。
掛け算の時と要領はそこまで変わらないはずです。
**恐れずにやってみろ！(これ大事)**
"
TheoremTab "^"

/--
## 説明
$x$を自然数とする。$x^1=x$である。
-/
TheoremDoc MyGame.pow_one as "pow_one" in "^"

/--
  自然数の累乗。
  pow_zero `a ^ 0 = 1` と、
  pow_succ `a ^ b′ = a ^ b * a`
  で定義される。
-/
DefinitionDoc MyGame.pow as "^"
NewDefinition MyGame.pow

/--
## 説明
$a$を自然数とする。$a^0=1$である。
-/
TheoremDoc MyGame.pow_zero as "pow_zero" in "^"

/--
## 説明
$a,b$を自然数とする。$a^b′=a^b\*a$である。
-/
TheoremDoc MyGame.pow_succ as "pow_succ" in "^"

NewTheorem MyGame.pow_zero MyGame.pow_succ

/--$∀x∈ℕ,x^1=x$-/
Statement pow_one (x:ℕ) : x ^ 1 = x := by
  rewrite[one_eq_succ_zero,pow_succ,pow_zero,one_mul]
  rfl

Conclusion "累乗も、意外と簡単ですね。。"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
