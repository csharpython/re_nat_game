import Game.Levels.Le.L01_zero_le
import Game.Levels.Le.L03_le_succ
import Game.Levels.Le.L04_le_trans
import Game.Levels.Le.L07_or_cases

World "Le"
Level 8

Title "補完(Le_total)"

namespace MyGame

Introduction "
`cases`をフル活用してみましょう！
"
TheoremTab "≤"
/--
## 説明
$a,b$を自然数とする。`a≤b`か`b′≤a`である。
-/
TheoremDoc MyGame.le_total as "le_total" in "≤"

/--$∀\{a,b\}∈ℕ²,a≤b∨b′≤a$-/
Statement le_total (a b:ℕ) : a ≤ b ∨ b′ ≤ a := by
  Hint(hidden := true)"まずは`induction a`！"
  induction a
  exact Or.inl (zero_le _)
  Hint(hidden := true)"つぎに∨のcases！"
  cases n_ih
  Hint(hidden := true)"さらに≤のcases！"
  cases h
  Hint(hidden := true)"ついでに`{w}`もcases！"
  cases w
  apply Or.inr
  exists 0
  rewrite[add_zero] at h_1
  rewrite[h_1,add_zero]
  rfl
  apply Or.inl
  exists a
  rewrite[h_1,succ_add,add_succ]
  rfl
  exact Or.inr ( le_trans _ n _ h ( le_succ n ))
Conclusion "
無事に`cases`を使いこなせましたね！
"
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
