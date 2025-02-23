import Game.Levels.MulEX
import Game.Levels.Pow
World "Challenge"
Level 2

Title "制作"

namespace MyGame

Introduction "
私はこのゲームを作ったきっかけについて話します。
私はNNG4を遊んでいました。なかなか興味深かったです。
さて、私はそのゲームを翻訳機を使いながらプレイしていました。
「NNG4をもっといろんな人に遊んでもらいたい」という思いから、NNG4の日本語版、
つまりこのゲームを作ろうと思ったのです。
"

TheoremTab "ℕ"

/--$(m^2-n^2)^2+(2mn)^2=(m^2+n^2)^2$-/
Statement pythagoras_numbers' (a b c:ℕ)(h:c+b^2=a^2) : c^2+(2*a*b)^2=(a^2+b^2)^2 := by
  rewrite[mul_pow,mul_pow,←h]-- Reduce a
  rewrite[add_assoc,←mul_two,pow_two (c+b^2*2),add_mul,mul_add c,←pow_two]
  rewrite[mul_comm c,add_assoc,←mul_add (b^2*2),←add_assoc,←mul_two,←add_mul,mul_comm (c+b^2),←mul_assoc]
  rewrite[mul_assoc (b^2),←pow_two,mul_comm (b^2),mul_assoc,mul_comm (c+b^2),←mul_assoc]
  rfl
Conclusion "
今はもうその目的は忘れられています...
しかし、このゲームの製作は、はっきり言って、楽しかったです。
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
