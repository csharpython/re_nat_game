import Game.Levels.Challenge.L02_Making
World "Challenge"
Level 3

Title "はじまりとおわり"

namespace MyGame

Introduction "
このゲームについて振り返りましょう。
今までいろいろなWorldに挑戦してきました。
Add,Le,Mul,MulEX,Parity,Coprime,Pow,
そして Challenge.

公理からはじまったこの旅は、今、終わりを迎えます。
"

TheoremTab "ℕ"
/--
## 説明
無限降下法。
-/
TheoremDoc MyGame.finite_decrease as "finite_decrease" in "ℕ"
/--無限降下法-/
Statement finite_decrease (f :ℕ → Prop)(h:∀(a:ℕ),f a→∃(b:ℕ),b′≤a∧f b) : ∀(x:ℕ),¬f x := by
  intro x
  apply complete_induction x
  intro a
  cases a<;>intro a i
  have ⟨b,⟨h,_⟩⟩ := h 0 i
  apply le_zero at h
  rewrite[eq_comm] at h
  exact zero_ne_succ b h
  have ⟨b,⟨p,r⟩⟩ := h (a_1′) i
  exact a b p r

Conclusion "
しかし、これからも数学というものは続いていき、終わりなき旅となるでしょう。
数学とLeanを、これからもよろしくお願いします。
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
