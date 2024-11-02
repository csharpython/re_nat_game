import Game.Metadata
import Game.MyObj.MyNat.Function
import Game.MyObj.MyNat.Numdef
import Game.Levels.Tutorial.L05_A1EqS

World "Tutorial"
Level 6

Title "BOSS:定理をつかおう"

namespace MyGame
Introduction"
(ボス戦の曲)

先ほど証明した定理`add_one_eq_succ`を使ってみましょう。
"

/--
## 説明
2は1の次です。
-/
TheoremDoc MyGame.two_eq_succ_one as "two_eq_succ_one" in "ℕ"

NewTheorem MyGame.two_eq_succ_one

/--$1+1=2$-/
Statement : (1 : MyNat) + 1 = 2 := by
  rewrite[add_one_eq_succ,two_eq_succ_one]
  rfl

Conclusion "
(ファンファーレのようなSE)

右上にある`</>`のようなボタンを押してみてください。
「エディターモード」に切り替えられ、数行のコードが表示されるでしょう。
カーソルをどこかの行に動かすと、その時点でのゴールが表示されます。
コピペを使って証明を保存しておくこともできます！
"
