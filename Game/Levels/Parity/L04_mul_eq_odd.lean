import Game.Levels.Parity.L02_odd_or_even
import Game.Levels.Parity.L03_odd_nand_even

World "Parity"
Level 4

Title "偶×奇"

namespace MyGame

Introduction "
奇数x奇数=奇数

同値関係について
「同値」とはなんでしょうか。
これはある二つの命題がともに真であるか、
ともに偽である事を示しています。
内部的には$P↔Q$は$P→Q∧Q→P$として扱われています!
**ちなみにrewriteもできます！**`

`have`について
示したいことがだんだん複雑になってきましたね...
こんな時、`have`を使うことで補題を示せます！
"

TheoremTab "2n"

/--
## 説明
二つの自然数の積が奇数なら二つの自然数は奇数
-/
TheoremDoc MyGame.mul_eq_odd as "mul_eq_odd" in "2n"

/--
## 説明
Andの導入則
-/
TheoremDoc And.intro as "And.intro" in "Prop"

/--
## 説明
ゴールを分解します。
todo
-/
TacticDoc constructor

/--$二つの自然数の積が奇数なら二つの自然数は奇数$-/
Statement mul_eq_odd(n m:ℕ) : odd (n*m) ↔ odd n ∧ odd m := by
  cases odd_or_even n
  cases h
  cases h_1
  rewrite[mul_comm,←mul_assoc]
  constructor <;> intro
  apply False.elim∘(odd_nand_even (m * w * 2))
  constructor
  exists (m * w)
  exact a
  cases a with l r
  apply False.elim∘(odd_nand_even (w * 2))
  constructor
  exists w
  exact l
  constructor <;> intro
  constructor ; exact h
  cases odd_or_even m
  cases h_1
  cases h_2
  rewrite[←mul_assoc] at a
  apply False.elim∘(odd_nand_even (n * w * 2))
  constructor
  exists n * w
  exact a
  exact h_1
  cases a
  cases left
  cases right
  cases h_1
  cases h_2
  rewrite[mul_add,mul_one,←mul_assoc,←add_assoc,←add_mul]
  exists (w*2+1)*w_1+w
Conclusion "
ポチ
"

/- Use these commands to add items to the game's inventory. -/

NewTactic constructor «have»
--NewTheorem NewTheorem eq_comm
-- NewDefinition Nat Add Eq
