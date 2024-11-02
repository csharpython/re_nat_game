import Game.Metadata
import Game.Levels.Mul.L05_one_mul

World "Multiplication"
Level 6

Title "倍増(two_mul)"

namespace MyGame

Introduction "
何で入れた？？？？
"

TheoremTab "*"

/--
## 説明
$n$を自然数とする。$2\*n=n+n$である。
-/
TheoremDoc MyGame.two_mul as "two_mul" in "*"

/--$∀n∈ℕ,2 × n = n + n$-/
Statement two_mul (n:ℕ) : 2 * n = n + n := by
  rewrite[two_eq_succ_one,succ_mul,one_mul]
  rfl
Conclusion "
これ絶対数合わせだよね？？？
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
