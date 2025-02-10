import Game.Levels.MulEX
import Game.MyObj.MyNat.Coprime

World "Coprime"
Level 1

Title "コプライム"

namespace MyGame

Introduction "
ようこそ、World Coprimeへ。
"

TheoremTab "Cop"

/--
## 説明
1と自然数は互いに素
-/
TheoremDoc MyGame.coprime_one as "coprime_one" in "Cop"
/--
  自然数が互いに素か判定する
-/
DefinitionDoc coprime as "coprime"


/--coprime 1 any-/
Statement coprime_one (n : ℕ) : coprime 1 n := by
  intro a b d h
  cases h
  rewrite[mul_comm] at left
  apply mul_right_eq_one at left
  exact left
Conclusion "
1となにかは互いに素
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
NewDefinition coprime
