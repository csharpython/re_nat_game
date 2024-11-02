import Game.Metadata
import Game.Levels.Mul.L04_mul_comm

World "Multiplication"
Level 7

Title "分散(mul_add)"

namespace MyGame

Introduction "
[ボス戦の曲]
"

TheoremTab "*"

/--
## 説明
$a,b,c$を自然数とする。$a(b+c)=ab+ac$である。
-/
TheoremDoc MyGame.mul_add as "mul_add" in "*"

/--$∀\{a,b,c\}∈ℕ³,a(b+c) = ab + ac$-/
Statement mul_add (a b c:ℕ) : a * (b + c) = a * b + a * c := by
  Branch
    induction a
    Hint (strict := true) "aの帰納法で始めるのだけはやめろ...正直言って、一番面倒だ..."
    repeat rewrite[zero_mul]
    rewrite[add_zero]
    rfl
    rewrite[succ_mul,succ_mul,succ_mul]
    rewrite[←add_assoc,←add_assoc,n_ih,add_right_comm (n*b)]
    rfl
  induction b
  rewrite[mul_zero]
  repeat rewrite[zero_add]
  rfl
  rewrite[succ_add,mul_succ,mul_succ,n_ih,add_right_comm]
  rfl
Conclusion "
🎉
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
