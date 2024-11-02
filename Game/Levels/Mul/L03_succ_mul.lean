import Game.Metadata
import Game.Levels.Mul.L02_zero_mul

World "Multiplication"
Level 3

Title "反転(succ_mul)"

namespace MyGame

Introduction "
足し算と要領は変わらないはずです。頑張れ！
"

TheoremTab "*"

/--
## 説明
$m,n$を自然数とする。$m′\*n=m\*n+n$である。
-/
TheoremDoc MyGame.succ_mul as "succ_mul" in "*"

/--$∀\{n,m\}∈ℕ²,m′ × n = m ⨯ n + n$-/
Statement succ_mul (m n:ℕ) : m′ * n = m * n + n := by
  Hint "他の定理の証明を振り返ってみることは大切です。意外と形が似ていることが多いです。"
  induction n
  rewrite[mul_zero,mul_zero,add_zero]
  rfl
  Hint (hidden := true) "`mul_succ`を使って、ゴールをシンプルにしてみましょう。"
  rewrite[mul_succ,mul_succ,n_ih]
  Hint (hidden := true) "うまいこと足す順番を入れ替えたら、証明できる気がしませんか？"
  rewrite[add_succ,add_succ,add_right_comm]
  rfl
Conclusion "
さて、`mul_comm`の証明に挑みましょう！
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
