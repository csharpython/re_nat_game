import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Add

World "Multiplication"
Level 1

Title "等倍(Mul_one)"

namespace MyGame

Introduction "
掛け算のチュートリアルです。
掛け算は、$n*0=0$と$m*n′=m*n+m$の2つで定義されます。
足し算の時と似ていますね。
足し算の時と要領はそこまで変わらないはずです。
**恐れずにやってみろ！(これ大事)**
"

TheoremTab "*"

/--
## 説明
$x$を自然数とする。$x*1=x$である。
-/
TheoremDoc MyGame.mul_one as "mul_one" in "*"

/--
  自然数の乗算。
  mul_zero `a * 0 = 0` と、
  mul_succ `a * b′ = a * b + a`
  で定義される。
-/
DefinitionDoc MyGame.mul as "*"
NewDefinition MyGame.mul

/--
## 説明
$a$を自然数とする。$a*0=a$である。
-/
TheoremDoc MyGame.mul_zero as "mul_zero" in "*"

/--
## 説明
$a,b$を自然数とする。$a\*b′=a*b+a$である。
-/
TheoremDoc MyGame.mul_succ as "mul_succ" in "*"

NewTheorem MyGame.mul_zero MyGame.mul_succ

/--$∀n∈ℕ,n × 1 = n$-/
Statement mul_one (n:ℕ) : n * 1 = n := by
  Hint "1って何だっけ?"
  rewrite[one_eq_succ_zero,mul_succ,mul_zero,zero_add]
  rfl

Conclusion "
掛け算も、意外と簡単ですね。
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
