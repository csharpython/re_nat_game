import Game.Levels.MulEX.L01_mul_eq_zero

World "MulEX"
Level 8

Title "Re:→"

namespace MyGame

Introduction "
マジかよ。(想定解23行)

## revert
新しいタクティク`revert`をアンロックしました。
`revert`は`intro`の逆のことをします。
...いつ使うの？
"
/--
## 説明
`intro`の逆です。
-/
TacticDoc revert

TheoremTab "*"

/--
## 説明
$a,b$を自然数とする。$x≠0$かつ$ax=bx$なら$a=b$である。
-/
TheoremDoc MyGame.mul_right_cancel as "mul_right_cancel" in "*"

/--$∀\{a,b,x\}∈ℕ³,(x≠0∧ax=bx)→ab≠0$-/
Statement mul_right_cancel (a b x:ℕ)(hx:x≠0)(h:a*x=b*x) : a=b := by
  Hint (hidden := true) "`revert {b}`"
  revert b
  Hint (hidden := true) "`induction {a}`"
  induction a with a h
  · intro b i
    rewrite[zero_mul,eq_comm] at i
    apply mul_eq_zero at i
    cases i with i i
    · rewrite[i]
      rfl
    · exact False.elim (hx i)
  · intro b
    Hint (hidden := true) "`cases {b}`"
    cases b with c hc
    · intro i
      rewrite[zero_mul,succ_mul] at i
      cases x with x x
      · apply False.elim∘hx
        rfl
      · rewrite[add_succ,eq_comm] at i
        exact False.elim (zero_ne_succ _ i)
    · rewrite[succ_mul,succ_mul]
      intro i
      apply add_right_cancel at i
      rewrite[h c i]
      rfl
Conclusion "
この問題はEXTRAの中でも最強...!
もう後はウィニングランです！
"

/- Use these commands to add items to the game's inventory. -/

NewTactic revert
-- NewTheorem eq_comm
-- NewDefinition Nat Add Eq
