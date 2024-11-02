import Game.Metadata
import Game.Levels.Mul.L03_succ_mul

World "Multiplication"
Level 4

Title "交換(mul_comm)"

namespace MyGame

Introduction "
足し算と要領は変わらないはずです。頑張れ！(2回目)
"

TheoremTab "*"

/--
## 説明
$m,n$を自然数とする。$m\*n=n\*m$である。
-/
TheoremDoc MyGame.mul_comm as "mul_comm" in "*"

/--$∀\{n,m\}∈ℕ²,m × n = n ⨯ m$-/
Statement mul_comm (m n:ℕ) : m * n = n * m := by
  induction n
  rewrite[mul_zero,zero_mul]
  rfl
  rewrite[mul_succ,succ_mul,n_ih]
  rfl
Conclusion "
まだ山場はたくさんあるぞ...!
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
