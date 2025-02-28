import Game.Levels.Mul.L05_one_mul

World "Multiplication"
Level 6

Title "倍増(mul_two)"

namespace MyGame

Introduction "
何で入れた？？？？
"

TheoremTab "*"

/--
## 説明
$n$を自然数とする。$n \times 2=n+n$である。
-/
TheoremDoc MyGame.mul_two as "mul_two" in "*"

/--$∀n∈ℕ,n \times 2= n + n$-/
Statement mul_two (n:ℕ) : n * 2 = n + n := by
  rewrite[two_eq_succ_one,mul_succ,mul_one]
  rfl
Conclusion "
これ絶対数合わせだよね？？？
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
