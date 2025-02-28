import Game.Levels.Mul.L08_add_mul

World "Multiplication"
Level 9

Title "Boss : 結合 (mul_assoc)"

namespace MyGame

Introduction "
[ボス戦のBGM]
"

TheoremTab "*"

/--
## 説明
$a,b,c$を自然数とする。$(ab)c=a(bc)$である。
-/
TheoremDoc MyGame.mul_assoc as "mul_assoc" in "*"

/--
## 説明
$a=b$なら$b=a$
-/
TheoremDoc eq_comm as "eq_comm" in "Prop"

/--$∀\{a,b,c\}∈ℕ³,a(bc) = (ab)c$-/
Statement mul_assoc (a b c:ℕ) : (a * b) * c = a * (b * c) := by
  Hint "とりあえず帰納法を使いましょう。
  先ほど証明した`mul_add`を活用できるはずです。
  今まで証明した定理を振り返るのも大事ですよ。"
  induction b
  rewrite[zero_mul,mul_zero,zero_mul]
  rfl
  rewrite[mul_succ,succ_mul,mul_add,add_mul,n_ih]
  rfl
Conclusion "
おつかれさま～
新しいワールド「World ^」に挑んでみて～
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
NewTheorem eq_comm
-- NewDefinition Nat Add Eq
