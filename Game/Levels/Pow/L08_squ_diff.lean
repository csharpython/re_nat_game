import Game.Levels.Pow.L07_pow_mul

World "Power"
Level 8

Title "因数(squ_diff)"

namespace MyGame

Introduction "
ごめん、さっき書いたの嘘だわ(後でこのレベル足しました)

このゲームに負の数はありません。では引き算はどうやって表現すればいいでしょうか？
"
TheoremTab "^"

/--
## 説明
$a,b,c$を自然数とする。$a=b+c$なら$a^2=(a+b)*c+b^2$である。
-/
TheoremDoc MyGame.squ_diff as "squ_diff" in "^"

/--$a^2-b^2=(a+b)(a-b)$-/
Statement squ_diff (a b c:ℕ)(hc:a=b+c) : a^2=(a+b)*c+b^2 := by
  rewrite[hc,pow_two,add_mul,mul_add,add_assoc,mul_comm c,add_comm,add_comm (b*c),←add_mul,pow_two]
  rfl
Conclusion "
これはきっといつか役立つはずです...
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
