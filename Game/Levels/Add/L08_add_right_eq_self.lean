import Game.Levels.Add.L07_add_left_cancel

World "Addition"
Level 8

Title "標的"

namespace MyGame
Introduction "
**警告：このレベルでは`rfl`が無効です。**

## rwの変種
`nth_rewrite`について紹介しましょう。
通常の`rw`は当てはまるものを**全部**置き換えますが、
`nth_rewrite x`はx番目だけ置き換えます！
"

DisabledTactic rfl
/--
## 説明
$x,y$を自然数とする。$x+y=x$なら$y=0$である。
-/
TheoremDoc MyGame.add_right_eq_self as "add_right_eq_self" in "+"

/--$∀\{x,y\}∈ℕ^2,x + y = x → y = 0$-/
Statement add_right_eq_self (x y:ℕ)(h:x + y = x) : y = 0 := by
  nth_rewrite 2 [←add_zero x] at h
  exact add_left_cancel y 0 x h

Conclusion "
実は、`exact add_left_cancel y 0 x h`などのようなコードは、
一部の変数を`_`で置き換えても動くことがあります。その際、それっぽい変数が自動的に設定されます！
E.g. `exact add_left_cancel _ _ _ h`
"

/--
## 説明
Why can you see this message?
-/
TacticDoc nth_rewrite

NewHiddenTactic nth_rewrite
/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
