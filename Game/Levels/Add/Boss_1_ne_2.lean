import Game.MyObj.MyNat.MyNat
import Game.MyObj.MyNat.Numdef
import Game.Metadata

World "Addition"
Level 10

Title "Boss:⊥"

namespace MyGame
Introduction "
## ⊥
数学には、正しいことだけではなく、間違っていることもあります。
例えば、$4=5$などです。これが間違っているを証明するにも、
`apply`と`exact`を使えます！
"

/--
## 説明
どんな自然数$x$でも$0≠x′$
-/
TheoremDoc MyGame.zero_ne_succ as "zero_ne_succ" in "ℕ"

/--$1≠2$-/
Statement (h:(1:ℕ) = 2) : False := by
  exact zero_ne_succ 0 (succ_inj 0 _ h)
Conclusion "
お疲れさまでした！このワールドで学んだことは数学上の様々なことに生かせます！
うまく使っていきましょう！
"

NewTheorem MyGame.zero_ne_succ
/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
