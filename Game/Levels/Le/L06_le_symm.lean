import Game.Levels.Le.L05_le_zero

World "Le"
Level 6

Title "双鏡(le_symm)"

namespace MyGame

Introduction "
Try It!
"
TheoremTab "≤"
/--
## 説明
$a,b$を自然数とする。$a≤b$かつ$b≤a$なら$a=b$である。
-/
TheoremDoc MyGame.le_symm as "le_symm" in "≤"

/--$∀\{a,b\}∈ℕ²,a ≤ b ∧ b ≤ a → a = b$-/
Statement le_symm (a b:ℕ)(h1 : a ≤ b)(h2 : b ≤ a) : a = b := by
  Hint "仮定で不等号は即`cases`!"
  cases h1
  cases h2
  Hint (hidden := true) "`a = a + w + w_1`"
  Branch
    rewrite[h_1] at h
    nth_rewrite 1 [←add_zero b,add_assoc] at h
    apply (add_left_cancel _ _ _) at h
    Hint (strict := true)(hidden := true) "`0 = {w_1}`を示しましょう。`cases {w_1}`でどうぞ。"
    cases w_1
    rewrite[h_1,add_zero]
    rfl
    rewrite[succ_add] at h
  rewrite[h] at h_1
  nth_rewrite 1 [←add_zero a,add_assoc] at h_1
  apply (add_left_cancel _ _ _) at h_1
  Hint (strict := true)(hidden := true) "`0 = {w}`を示しましょう。`cases {w}`でどうぞ。"
  cases w
  rewrite[h,add_zero]
  rfl
  rewrite[succ_add] at h_1
  exact False.elim (zero_ne_succ _ h_1)
Conclusion "
おつかれ！
"
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
