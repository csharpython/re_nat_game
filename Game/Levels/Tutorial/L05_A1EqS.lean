import Game.Metadata
import Game.MyObj.MyNat.Function
import Game.MyObj.MyNat.Numdef

World "Tutorial"
Level 5

Title "定理をつくろう(succ_eq_add_one)"

namespace MyGame
Introduction"
$a + (0でない適当な自然数)$ に関する定義も欲しいですよね？
作っておきました

Leanでは、自分で定理を作って証明し、ほかの定理の証明に生かすといったことができます。
やってみましょう！
"

/--
## 説明
$a,b$を自然数とする。$a + b′ = (a + b)′$ である。
-/
TheoremDoc MyGame.add_succ as "add_succ" in "+"

TheoremTab "ℕ"
/--
## 説明
1は0の次です。
-/
TheoremDoc MyGame.one_eq_succ_zero as "one_eq_succ_zero" in "ℕ"

/--
## 説明
$a$が自然数なら、$a+1=a′$である。 -/
TheoremDoc MyGame.add_one_eq_succ as "add_one_eq_succ" in "+"

NewTheorem MyGame.add_succ MyGame.one_eq_succ_zero

/--$∀a∈ℕ,a+1=a′$-/
Statement add_one_eq_succ {a : ℕ} : a + 1 = a′ := by
  Hint "$1$の定義はなんでしたか？"
  rewrite[one_eq_succ_zero,add_succ,add_zero]
  rfl

Conclusion "
「定義から考える」というコツは意外と有用です。
"
