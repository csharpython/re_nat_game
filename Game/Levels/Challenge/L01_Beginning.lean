import Game.Levels.MulEX
import Game.Levels.Coprime
import Game.Levels.Pow
World "Challenge"
Level 1

Title "始発点"

namespace MyGame

Introduction "
私がLean4を知ったきっかけについて話しましょう。
ある日、私は数学について色々調べていました。
その時、Lean4と自動証明についての動画を見つけました。
私がLean4に興味を持ったのは、それからでした。

# Prop
Propとは何でしょうか？Propとは、命題の事です。
"

TheoremTab "ℕ"

/--
## 説明
完全帰納法です。
-/
TheoremDoc MyGame.complete_induction as "complete_induction" in "ℕ"
/--完全帰納法-/
Statement complete_induction (n:ℕ)(P:ℕ→Prop)(h:∀a,(∀b,b′≤a→P b)→P a) : P n := by
  have h2 : ∃w,n≤w
  exists n
  exact le_rfl n
  cases h2
  revert n
  induction w
  intro n i
  cases le_zero n i
  apply h 0
  intro b h
  have h := le_zero (b′) h
  rewrite[eq_comm] at h
  exact False.elim (zero_ne_succ b h)
  intro m hm
  cases le_total m n
  exact n_ih m h_1
  cases le_symm _ _ hm h_1
  apply h
  intro b h
  apply n_ih
  cases h
  exists w
  rewrite[succ_add] at h_2
  exact succ_inj _ _ h_2
Conclusion "
そして私がNNG4について知ったのもそれがきっかけでした。
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
