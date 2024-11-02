import Game.Levels.Mul
import Game.Levels.Le

World "MulEX"
Level 6

Title "(*‘∀‘)"

namespace MyGame


Introduction "
**exact、apply無効**(余裕があればなぜ無効なのか考えてみよう！)

## 全称記号
∀←これです。
`∀(a:ℕ),P a`は、
全ての$a$に対して$P a$を満たすということを表します。
`intro`が使えます。
"

/--
  `∀x,P x`は、全ての`x`で`P x`であることを表しています。
  直接入力するなら`\all`を使おう！
-/
DefinitionDoc Forall as "∀"
NewDefinition Forall

DisabledTactic exact apply
/--$∃e∈ℕ,∀n∈ℕ,ne=n$-/
Statement : ∃(e:ℕ),∀(n:ℕ),n*e=n := by
  exists 1
  intro
  rewrite[mul_one]
  rfl

Conclusion "
これはまだ準備段階にすぎません...
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
