import Game.Levels.MulEX.L01_mul_eq_zero

World "MulEX"
Level 9

Title "1*1"

namespace MyGame

Introduction "
`mul_eq_zero`と見た目だけ似ていますね。見た目だけ。
"
TheoremTab "*"

/--
## 説明
$a,b$を自然数とする。$ab=1$なら$a=1$である。
-/
TheoremDoc MyGame.mul_right_eq_one as "mul_right_eq_one" in "*"

/--$∀\{a,b\}∈ℕ²,ab=1→b=1$-/
Statement mul_right_eq_one (a b:ℕ)(h:a*b=1) : a=1 := by
  cases a with a a
  rewrite[zero_mul] at h
  exact False.elim (zero_ne_succ 0 h)
  cases a with a a
  rewrite[one_eq_succ_zero]
  rfl
  cases b with b b
  rewrite[mul_zero] at h
  exact False.elim (zero_ne_succ 0 h)
  rewrite[mul_succ,add_succ,add_succ,eq_comm] at h
  exact False.elim (zero_ne_succ _ (succ_inj _ _ h))
Conclusion "
お疲れ様です。
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic revert
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
