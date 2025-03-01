import Game.Levels.Coprime.L02_coprime_comm

World "Coprime"
Level 3

Title "否定"

namespace MyGame

Introduction "
「互いに素」の否定はなんでしょう？
"

TheoremTab "Cop"

/--
## 説明
「互いに素」の否定
-/
TheoremDoc MyGame.not_coprime as "not_coprime" in "Cop"


/--$¬\operatorname{coprime} n\ m↔...$-/
Statement not_coprime (n m : ℕ) : ¬coprime n m ↔ ∃(a b d:ℕ),a*d=n∧b*d=m∧d≠1 := by
  rewrite[coprime]
  constructor
  <;> intro h
  <;> contrapose! h
  <;> intro a b d i
  exact h a b d i.left i.right
  intro j
  exact h a b d ⟨i,j⟩
Conclusion "
対偶って便利だね
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic push_neg
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
