import Game.Metadata
import Game.MyObj.MyNat.Function

World "Tutorial"
Level 3

Title "逆走"

namespace MyGame
Introduction"
## 逆方向の置き換え
(Lv2で見つけた人もいるかもしれませんが)
実は`h : X=Y`という仮定がある場合、
ゴールの`X`を`Y`に置き換えるだけでなく、
**`Y`を`X`に置き換えることもできます**
早速試してみましょう！
"

/--$x,y,z$が全て自然数で、$z=x$かつ$z=y$なら$x+y=z+z$。-/
Statement (x y z:ℕ)(h1 : z = x)(h2 : z = y) : x + y = z + z := by
  Hint (hidden := true) "`rewrite`のマニュアルは読みましたか？"
  Branch
    rewrite[h2] at h1
    Hint (strict := true) "イースターエッグ発見！ #2"
    rewrite[h2,h1]
    rfl
  Branch
    rewrite[h1] at h2
    Hint (strict := true) "イースターエッグ発見！ #2"
    rewrite[h1,h2]
    rfl
  rewrite[←h1,←h2]
  rfl

Conclusion "このように、数学では
「逆から考える」というテクニックが有効なことがあります。
ゴールを閉じるために必要なことを考えると、
自ずと答えが見えてくるでしょう。
"
