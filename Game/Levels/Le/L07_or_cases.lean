import Game.Metadata
import Game.Levels.Add.L07_add_left_cancel

World "Le"
Level 7

Title "論理和"

namespace MyGame

Introduction "
`cases`が使える命題をもう一つ紹介します。
`P ∨ Q`にたいし`cases`を使うと、
`P`の場合のゴールと
`Q`の場合のゴールが生成されます！
"

/--
## 説明
$P$とする。$P∨Q$である。
-/
TheoremDoc Or.inl as "Or.inl" in "Prop"
/--
## 説明
$Q$とする。$P∨Q$である。
-/
TheoremDoc Or.inr as "Or.inr" in "Prop"
NewTheorem Or.inl Or.inr

/--$∀a∈ℕ,(a = 50 ∨ a = 73) → (a = 73 ∨ a = 50)$-/
Statement (a:ℕ)(h : a = 50 ∨ a = 73) : a = 73 ∨ a = 50 := by
  Hint "そうですね、`cases h`です"
  cases h with L R
  exact Or.inr L
  exact Or.inl R
Conclusion "
このレベルは非常に簡単です。
つまり、**この次のレベルがめちゃくちゃ難しい**ってこと！
"
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
