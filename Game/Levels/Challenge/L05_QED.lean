import Game.Levels.Challenge.L04_History
World "Challenge"
Level 5

Title "Quod Erat Demonstrandum"

namespace MyGame

Introduction "
ついにここまでたどり着きました。
"

TheoremTab "ℕ"
/--$a^4+b^4≠z^4$-/
Statement (a b c:ℕ)(ane0 : a≠0)(bne0 : b≠0) : a^4+b^4≠c^4 := by
  have www (c2:ℕ) : a^4+b^4≠(c2)^2
  sorry
  have www2 := www (c^2)
  rewrite[] at www2
Conclusion "
「公理」は基礎であり、それゆえ少し異なるだけでまったく違った結論が得られます。
非ユークリッド幾何学がその例です。
基礎を固めることは重要です。
さて、とうとうその基礎からとある事実を証明する時が来ました。
検討を、祈ります。100行くらいあるこの証明をした君ならできるはずです。
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

NewTheorem MyNat.nameless_1 MyNat.nameless_2 MyGame.squ_inj
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
