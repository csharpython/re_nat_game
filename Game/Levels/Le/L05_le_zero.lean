import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Add
import Game.MyObj.MyNat.Le

World "Le"
Level 5

Title "Boss:虚像(le_zero)"

namespace MyGame

Introduction "
World Add-10で出てきたFalseのことを覚えていますか？
Falseからはどんな命題も導けます。
このステージは、Falseを何とかして導くことがポイントです！
"
TheoremTab "≤"

/--
## 説明
偽を仮定すれば、全ての命題が真である。
-/
TheoremDoc False.elim as "False.elim" in "Prop"
NewTheorem False.elim
/--
## 説明
$a$を自然数とする。$a≤0$なら$a=0$である。
-/
TheoremDoc MyGame.le_zero as "le_zero" in "≤"

/--$∀a∈ℕ,a ≤ 0 → a = 0$-/
Statement le_zero (a:ℕ)(h : a ≤ 0) : a = 0 := by
  Hint "まずは∃のcasesから始めよう"
  cases h
  Hint (hidden := true) "次に自然数のcasesをしよう"
  cases a
  rfl
  Hint (hidden := true) "Falseを導くためには...?"
  rewrite[succ_add] at h_1
  exact False.elim (zero_ne_succ _ h_1)
Conclusion "
おつかれ！
"
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
