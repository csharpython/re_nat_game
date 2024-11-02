import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Add
import Game.MyObj.MyNat.Le

World "Le"
Level 1

Title "虚無以上(zero_le)"

namespace MyGame

Introduction "
## $∃$
$∃$について説明しましょう。
$∃v,P(v)$は$P(v)$を満たす$v$があることを表しています。
このような形の命題を証明するときは、条件を満たす具体的な値`w`を見つけ、

## `exists w`

を使えばよいです！

## ≤の意味
`a ≤ b`と`∃ (c : ℕ), b = a + c`は同じ意味です。
そのため、`exists`が使えます！
"

TheoremTab "≤"

/--
## 説明
$n$を自然数とする。$0≤n$である。
-/
TheoremDoc MyGame.zero_le as "zero_le" in "≤"

/--
  自然数の大小比較
  `a ≤ b ↔ ∃ (c : ℕ), b = a + c`
-/
DefinitionDoc MyGame.le as "≤"


/--
  `∃x,P x`は、P xを満たすxが存在することを表しています。
  直接入力するなら`\ex`を使おう！
-/
DefinitionDoc Exists as "∃"

NewDefinition MyGame.le Exists

/--
## 説明
`∃v,P(v)`に対して、`exists w`を使うと、ゴールが`P(w)`に変化します。
-/
TacticDoc «exists»

/--$∀n∈ℕ,0 ≤ n$-/
Statement zero_le (n:ℕ) : 0 ≤ n := by
  Hint "`exists n`"
  exists n
  rewrite[zero_add]
  rfl
Conclusion "
≤も、意外と簡単ですね。
"

NewTactic «exists»
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
