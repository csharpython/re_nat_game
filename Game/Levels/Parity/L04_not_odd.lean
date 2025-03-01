import Game.Levels.Parity.L03_odd_nand_even

World "Parity"
Level 4

Title "¬奇↔偶"

namespace MyGame

Introduction "
同値関係について
「同値」とはなんでしょうか。
これはある二つの命題がともに真であるか、
ともに偽である事を示しています。
内部的には$P↔Q$は$P→Q∧Q→P$として扱われています!
**ちなみにrewriteもできます！**`

# `constructor`
`constructor`はゴールを分解するタクティクです！
"

TheoremTab "2n"

/--
## 説明
奇数でない自然数は偶数
-/
TheoremDoc MyGame.not_odd as "not_odd" in "2n"

/--
## 説明1：Andの分解
`P∧Q`に対して、`constructor`を使うと、ゴールが`P`と`Q`に変化します。

## 説明2：同値の分解
`P↔Q`に対して、`constructor`を使うと、ゴールが`P→Q`と`Q→P`に変化します。
-/
TacticDoc constructor
/--$∀n∈ℕ,¬\operatorname{odd} n↔\operatorname{even} n$-/
Statement not_odd(n:ℕ) : ¬odd n↔even n := by
  constructor <;> intro
  cases odd_or_even n
  exact h
  exact False.elim (a h)
  intro b
  exact odd_nand_even n ⟨a,b⟩
Conclusion "
これはよく使う補題です。これで、これを使うときに各コードが1行で済みます！
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

NewTactic constructor
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
