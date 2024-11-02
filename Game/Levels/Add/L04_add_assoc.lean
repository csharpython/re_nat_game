import Game.Metadata
import Game.Levels.Add.L01_zero_add
import Game.Levels.Add.L02_succ_add

World "Addition"
Level 4

Title "結合法則(add_assoc)"

namespace MyGame

Introduction "
$x+y+z$について話しましょう。
これは、$(x+y)+z$でしょうか？それとも、$x+(y+z)$でしょうか？
正解は、当然$(x+y)+z$です。+は左から計算するからね。
では$(x+y)+z$と$x+(y+z)$にはどのような関係があるのでしょうか？
それを調べてみましょう。
"

/--
## 説明
x yを自然数とする。x+y=y+xである。
-/
TheoremDoc MyGame.add_assoc as "add_assoc" in "+"

/--$∀\{x,y,z\}∈ℕ^3,x + y + z = x + (y + z)$-/
Statement add_assoc (x y z:ℕ) : x + y + z = x + (y + z) := by
  Hint "たぶんzに対して帰納法するのが一番楽です。"
  induction z
  repeat rewrite[add_zero]
  rfl
  rewrite[add_succ,add_succ,add_succ,n_ih]
  rfl
Conclusion "
私の回答を載せておきますね：
```
induction z
repeat rewrite[add_zero]
rfl
rewrite[add_succ,add_succ,add_succ,n_ih]
rfl
```
"

/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
