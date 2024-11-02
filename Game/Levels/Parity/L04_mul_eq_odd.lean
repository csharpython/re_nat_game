import Game.Levels.Parity.L02_odd_or_even

World "Parity"
Level 4

Title "偶奇-4"

namespace MyGame

Introduction "
奇数x奇数=奇数
"

TheoremTab "2n"

/--
## 説明
二つの自然数の積が奇数なら二つの自然数は奇数
-/
TheoremDoc MyGame.mul_eq_odd as "mul_eq_odd" in "2n"


/--$二つの自然数の積が奇数なら二つの自然数は奇数$-/
Statement mul_eq_odd(n m:ℕ)(h:odd (n*m)) : odd n := by
  cases odd_or_even n with h2
  cases h2 with x h2
  rewrite[←h2] at h

Conclusion "
Q.何でこんな難しいんですか?

A.私も同意見です
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic obtain
--NewTheorem NewTheorem eq_comm
-- NewDefinition Nat Add Eq
