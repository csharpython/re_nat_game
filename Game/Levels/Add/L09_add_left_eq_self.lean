import Game.Levels.Add.L08_add_right_eq_self

World "Addition"
Level 9

Title "Cor."

namespace MyGame
Introduction "
**警告：このレベルでは`rfl`が無効です。**
## 系
ある定理について、
そこから簡単に(明らかであるとして証明が省略されるくらいに)証明できる定理です。
これもその一例ですね。
"

/--
## 説明
$x,y$を自然数とする。$x+y=y$なら$x=0$である。
-/
TheoremDoc MyGame.add_left_eq_self as "add_left_eq_self" in "+"


DisabledTactic rfl
/--$∀{x,y}∈ℕ^2,x + y = y → x = 0$-/
Statement add_left_eq_self (x y:ℕ)(h:x + y = y) : x = 0 := by
  rewrite[add_comm] at h
  exact add_right_eq_self y x h
Conclusion "
`apply`と`exact`を使いこなせましたか？さあ、次のレベルで確認してみましょう！
"
/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
