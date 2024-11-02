import Game.Levels.Mul
import Game.Levels.Le

World "MulEX"
Level 1

Title "因数分解(mul_eq_zero)"

namespace MyGame

Introduction "
ハードモードへようこそ。
"

TheoremTab "*"

/--
## 説明
$a=b$なら$b=a$
-/
TheoremDoc eq_comm as "eq_comm" in "Prop"

/--
## 説明
$a,b$を自然数とする。$ab=0$なら$a=0$か$b=0$である。
-/
TheoremDoc MyGame.mul_eq_zero as "mul_eq_zero" in "*"

/--$∀\{a,b\}∈ℕ² ,ab = 0 → a=0∨b=0$-/
Statement mul_eq_zero (a b:ℕ)(h:a*b=0) : a = 0 ∨ b = 0:= by
  Hint(hidden := true) "`cases`でどうぞ"
  cases a with a
  apply Or.inl
  rfl
  cases b with b
  apply Or.inr
  rfl
  rewrite[mul_succ,add_succ,eq_comm] at h
  exact False.elim (zero_ne_succ _ h)
Conclusion "
次行きましょう。
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
NewTheorem eq_comm
-- NewDefinition Nat Add Eq
