import Game.Levels.Coprime.L01_introduce

World "Coprime"
Level 2

Title "対称性"

namespace MyGame

Introduction "
対称性っていいよね。
"

TheoremTab "Cop"

/--
## 説明
「互いに素」の対称性
-/
TheoremDoc MyGame.coprime_comm as "coprime_comm" in "Cop"


/--$\operatorname{coprime} n\ m ↔ \operatorname{coprime} m\ n$-/
Statement coprime_comm (n m : ℕ) : coprime n m ↔ coprime m n := by
  constructor
  <;> intro h a b d i
  <;> exact h b a d (And.intro i.right i.left)
Conclusion "
# Q.対称性ってなんでいいの？
A.利用することで複雑な問題が一気にシンプルになることがある！
そうでなくてもある程度楽できる！
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
