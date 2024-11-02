import Game.Metadata
import Game.Levels.Pow.L01_pow_one
import Game.Levels.Pow.L03_one_pow
import Game.Levels.Pow.L05_mul_pow

World "Power"
Level 7

Title "乗数(pow_mul)"

namespace MyGame

Introduction "
$x^{y^z}$について話しましょう。
これは、$(x^y)^z$でしょうか？それとも、$x^{(y^z)}$でしょうか？
正解は、当然$x^{(y^z)}$です。^は右から計算するからね。
...これ、前に書いたことがあるような...?
"
TheoremTab "^"

/--
## 説明
$x,a,b$を自然数とする。$(x ^ a) ^ b= x^{ab}$である。
-/
TheoremDoc MyGame.pow_mul as "pow_mul" in "^"

/--$∀\{x,a,b\}∈ℕ³→(x^a)^b=x^{ab}$-/
Statement pow_mul (x a b:ℕ) : (x^a)^b = x ^ (a * b) := by
  Hint(hidden := true) "まあ、`induction a`ですね。"
  induction a
  rewrite[zero_mul,pow_zero,one_pow]
  rfl
  rewrite[pow_succ,mul_pow,succ_mul,pow_add,n_ih]
  rfl

Conclusion "そろそろ気づいてる人もいると思いますが、
`World ^`はすべて今までのステージが元ネタになっています。"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
