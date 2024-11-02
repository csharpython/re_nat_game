import Game.Metadata
import Game.Levels.Add.L03_Add_comm
import Game.Levels.Add.L04_add_assoc


World "Addition"
Level 5

Title "指定(add_right_comm)"

namespace MyGame

Introduction "さあ、先ほど証明した定理を使ってみましょう。
実は、定理はそのまま使うだけではなく、変数を指定して使うこともできます。
例えば、`rw[add_comm y]`を`x+(y+z)`に対して使うと、
`(y+z)+x`ではなく`x+(z+y)`にできます！
"

/--
## 説明
$x,y,z$を自然数とする。$x+y+z=x+z+y$である。
-/
TheoremDoc MyGame.add_right_comm as "add_right_comm" in "+"

/--$∀\{x,y,z\}∈ℕ^3,x + y + z = x + z + y$-/
Statement add_right_comm (x y z:ℕ) : x + y + z = x + z + y := by
  Hint "先ほど証明した結合法則が使えないでしょうか？"
  rewrite[add_assoc,add_comm y,←add_assoc]
  rfl
Conclusion "
私の回答を載せておきますね：
```
rewrite[add_assoc,add_comm y,←add_assoc]
rfl
```
"

/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
