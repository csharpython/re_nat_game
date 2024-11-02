import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Add
import Game.MyObj.MyNat.Le

World "Le"
Level 2

Title "それはそれ以上(le_rfl)"

namespace MyGame

Introduction "
「以上」って、(数学ではもちろん$≥$ですが)
$>$として使われることも$≥$として使われることもありますよね。
なんでなんでしょうか。
"

TheoremTab "≤"


/--
## 説明
$n$を自然数とする。$n≤n$である。
-/
TheoremDoc MyGame.le_rfl as "le_rfl" in "≤"

/--$∀n∈ℕ,n ≤ n$-/
Statement le_rfl (n:ℕ) : n ≤ n := by
  Hint(hidden := true) "add_zero"
  exists 0
  rewrite[add_zero]
  rfl
Conclusion "
誰かわかる人、教えてください
"
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
