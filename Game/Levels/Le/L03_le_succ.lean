import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Add
import Game.MyObj.MyNat.Le

World "Le"
Level 3

Title "一歩ずつ前へ(le_succ)"

namespace MyGame

Introduction "
一歩ずつ前へ、進んでいきましょう。
「千里の道も一歩から」です。
"

TheoremTab "≤"


/--
## 説明
$n$を自然数とする。$n≤n′$である。
-/
TheoremDoc MyGame.le_succ as "le_succ" in "≤"

/--$∀n∈ℕ,n ≤ n′$-/
Statement le_succ (n:ℕ) : n ≤ n′ := by
  Hint(hidden := true) "add_one_eq_succ"
  exists 1
  rewrite[add_one_eq_succ]
  rfl
Conclusion "
使える定理を振り返ることはいつでも大事ですよ！
"
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
