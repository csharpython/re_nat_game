import Game.Levels.MulEX.L03_le_mul_right

World "MulEX"
Level 4

Title "複製失敗(mul_right_eq_one)"

namespace MyGame

Introduction "
等倍！
"

TheoremTab "*"

/--
## 説明
$a,b$を自然数とする。$a′b=a′$なら$b=1$である。
-/
TheoremDoc MyGame.mul_eq_self as "mul_eq_self" in "*"

/--$∀\{a,b\}∈ℕ²,a′b=a′→b=1$-/
Statement mul_eq_self (a b:ℕ)(h:a′*b=a′) : b=1 := by
  Hint(hidden := true) "`cases`でどうぞ。案の定。"
  cases b
  rewrite[mul_zero] at h
  exact False.elim (zero_ne_succ _ h)
  Hint(hidden := true) "ここで`{h}`の左辺を`?+{a}′`の形で表してみましょう"
  rewrite[mul_succ] at h
  apply add_left_eq_self at h
  Hint(hidden := true)(strict := true) "因数分解"
  apply mul_eq_zero at h
  cases h
  rewrite[eq_comm] at h_1
  exact False.elim (zero_ne_succ _ h_1)
  rewrite[h_1,one_eq_succ_zero]
  rfl
Conclusion "
なんか`cases`の役割多くない？やっぱり。
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
