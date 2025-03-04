import Game.Levels.Challenge.L01_Beginning

World "Challenge"
Level 2

Title "複雑さと美しさ"

namespace MyGame

Introduction "
ええ、この問題は複雑そうです。
ですが私がこれをChallenge-2としたのには理由があります。
これの逆は(実際にはもう少し複雑ですが)、フェルマーの最終定理のn=4の場合の証明に使われています。
ゆえに...というには少し違うかもしれませんが、「シンプルさ」と「美しさ」は別物です。
"

TheoremTab "ℕ"
/--
## 説明
ピタゴラス数を生成する式。
-/
TheoremDoc MyGame.pythagoras_numbers' as "pythagoras_numbers'" in "ℕ"
/--$(m^2-n^2)^2+(2mn)^2=(m^2+n^2)^2$-/
Statement pythagoras_numbers' (a b c:ℕ)(h:c+b^2=a^2) : c^2+(2*a*b)^2=(a^2+b^2)^2 := by
  rewrite[mul_pow,mul_pow,←h]-- Reduce a
  rewrite[add_assoc,←mul_two,pow_two (c+b^2*2),add_mul,mul_add c,←pow_two]
  rewrite[mul_comm c,add_assoc,←mul_add (b^2*2),←add_assoc,←mul_two,←add_mul,mul_comm (c+b^2),←mul_assoc]
  rewrite[mul_assoc (b^2),←pow_two,mul_comm (b^2),mul_assoc,mul_comm (c+b^2),←mul_assoc]
  rfl
Conclusion "
ですが、数学者が単純で奥深いものに心惹かれるという点では正しいかもしれません。たぶん。
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
