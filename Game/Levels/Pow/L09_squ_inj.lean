import Game.Levels.Pow.L08_squ_diff

--World "Power"
--Level 9

--Title "平方(squ_inj)"

namespace MyGame

--Introduction "
--平方根も同様に考えられないでしょうか？
--"
--TheoremTab "^"

/--
## 説明
$a,b$を自然数とする。$a^2=b^2$なら$a=b$である。
-/
TheoremDoc MyGame.squ_inj as "squ_inj" in "^"

/--$a^2=b^2→a=b$-/
theorem squ_inj (a b:ℕ)(h:a^2=b^2) : a=b := by
  sorry
Conclusion "
これはきっといつか役立つはずです...
"

/- Use these commands to add items to the game's inventory. -/

-- NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
