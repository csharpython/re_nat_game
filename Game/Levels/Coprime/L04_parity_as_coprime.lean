import Game.Levels.Coprime.L03_not_coprime

World "Coprime"
Level 4

Title "帰着"

namespace MyGame

Introduction "
互いに素　と　偶奇　の関係について。
"

TheoremTab "Cop"

/--
## 説明
「2と互いに素」と「奇数である」は同値
-/
TheoremDoc MyGame.coprime_two as "coprime_two" in "Cop"


/--coprime 2 n↔odd n-/
Statement coprime_two (n : ℕ) : coprime 2 n ↔ odd n := by
  constructor <;> intro h
  <;> contrapose! h
  <;> rewrite[not_coprime] at *
  cases odd_or_even n
  cases h_1
  exists 1,w,2
  constructor;exact one_mul 2
  constructor;exact h_2
  intro F
  rewrite[two_eq_succ_one,one_eq_succ_zero,eq_comm] at F
  apply succ_inj at F
  exact False.elim (zero_ne_succ 0 F)
  exact False.elim (h h_1)
  have div2 (x y:ℕ)(i : x*y=2) : x=1∨x=2 := by
    cases x
    rewrite[zero_mul] at i
    exact False.elim (zero_ne_succ 1 i)
    cases a
    apply Or.inl
    rfl
    cases a_1
    apply Or.inr
    rfl
    cases y
    rewrite[mul_zero] at i
    exact False.elim (zero_ne_succ 1 i)
    rewrite[mul_succ] at i
    repeat rewrite[add_succ] at i
    rewrite[eq_comm] at i
    exact False.elim (zero_ne_succ _ (succ_inj 0 _ (succ_inj 1 _ i)))
  cases h with a h
  cases h with b h
  cases h with d h
  rewrite[mul_comm] at h
  cases div2 d a h.left
  exact False.elim (h.right.right h_1)
  cases h_1
  have k : even n := by
    exists b
    rewrite[h.right.left]
    rfl
  intro v
  exact odd_nand_even n ⟨k,v⟩
Conclusion "
え～想定解は43行です。
ですがこれで、偶奇の問題を「互いに素」の問題として扱うことができるようになりました。
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

-- NewTactic push_neg
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
