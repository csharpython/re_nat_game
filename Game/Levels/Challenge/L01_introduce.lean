import Game.Levels.MulEX
import Game.Levels.Coprime
import Game.Levels.Pow
World "Challenge"
Level 1

Title "始発点"

namespace MyGame

Introduction "
私がLean4を知ったきっかけについて話しましょう。
ある日、私は数学について色々調べていました。
その時、Lean4と自動証明についての動画を見つけました。
私がLean4に興味を持ったのは、それからでした。
"

/--TODO THIS STATEMENT-/
Statement(m n:ℕ) : m^2≠n*3+2 := b
  sorry
Conclusion "
0は偶数ですね！
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
NewDefinition even
