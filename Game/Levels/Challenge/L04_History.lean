import Game.Levels.Challenge.L03_Memory
import Game.Levels.Pow.L09_squ_inj
import Game.MyObj.MyNat.Bonus
World "Challenge"
Level 4

Title "歴史"

namespace MyGame

Introduction "
ユークリッド原論について知っているでしょうか？
これは「公理」という概念が明確に示された本の中で、最古のものとされています。
現代の数式や数学理論に通じる基礎を築いた本ですね。
"

TheoremTab "ℕ"
/--
## 説明
ピタゴラス数が自然数$m,n$を用いて$(m^2-n^2,2mn,m^2+n^2)$と表せること。
-/
TheoremDoc MyGame.pythagoras_numbers as "pythagoras_numbers" in "ℕ"

/--
## 説明
互いに素な自然数$x,y$の積が何かの2乗なら$x$は何かの2乗
-/
TheoremDoc MyNat.nameless_1 as "nameless_1" in "ℕ"

/--
## 説明
互いに素な自然数$x,y$の積が$z$の2乗なら$x$と$z$は互いに素
-/
TheoremDoc MyNat.nameless_2 as "nameless_2" in "ℕ"


/--$(m^2-n^2)^2+(2mn)^2=(m^2+n^2)^2$-/
Statement pythagoras_numbers (a b c:ℕ)(h:a^2+b^2=c^2)(hc : coprime a b)(he : even b) : ∃(x y:ℕ),a+x^2=y^2∧b=2*x*y∧c=x^2+y^2 := by
  have ho : odd a := by
    cases he
    rewrite[←not_even]
    intro k
    contrapose! hc
    rewrite[not_coprime a b]
    cases k
    exists w_1,w,2
    constructor
    exact h_2
    constructor
    exact h_1
    intro v
    apply succ_inj 1 0 at v
    rewrite[eq_comm] at v
    exact zero_ne_succ 0 v
  have alec : a≤c := by
    cases le_total a c
    exact h_1
    cases h_1
    cases h_2
    rewrite[pow_two,add_mul,mul_add,mul_succ,succ_mul,←pow_two] at h
    repeat rewrite[add_assoc] at h
    apply add_right_eq_self at h
    rewrite[succ_add,add_succ,eq_comm] at h
    exact False.elim (zero_ne_succ _ h)
  cases alec
  have hco : odd c := by
    have hc2o : odd (c^2) := by
      rewrite[←h,←not_even,add_eq_even,pow_two,pow_two,←not_odd,←not_odd,mul_eq_odd,mul_eq_odd]
      contrapose! ho
      contrapose! ho
      apply Or.inr
      constructor
      constructor <;> exact ho
      intro k _
      exact odd_nand_even b ⟨he,k⟩
    rewrite[pow_two,mul_eq_odd] at hc2o
    exact hc2o.left
  have v := squ_diff c a w h_1
  have ocaa : even (c + a) := by
    rewrite[add_eq_even]
    constructor <;> intro z <;> apply False.elim
    exact odd_nand_even c ⟨z,hco⟩
    exact odd_nand_even a ⟨z,ho⟩
  have ocsa : even w := by
    contrapose! hco
    intro v
    rewrite[h_1,←not_even,add_eq_even] at v
    apply v
    constructor <;> intro
    rewrite[←not_even] at ho
    exact False.elim (ho a_1)
    exact False.elim (hco a_1)
  cases ocaa
  cases ocsa
  cases he
  have hcc : c*2=(w_1+w_2)*2 := by
    rewrite[add_mul,h_2,h_3,add_assoc,←h_1,mul_two]
    rfl
  apply mul_right_cancel at hcc
  have hac : (a+w_2)*2=w_1*2 := by
    rewrite[add_mul,h_2,h_3,mul_two,add_assoc,←h_1,add_comm]
    rfl
  apply mul_right_cancel at hac
  have b2caw : b^2=(c+a)*w := by
    rewrite[←h,add_comm] at v
    apply add_right_cancel at v
    exact v
  have u2st : w_3^2=w_1*w_2 := by
    apply mul_right_cancel _ _ (2^2)
    intro k
    rewrite[eq_comm,pow_two,mul_two,two_eq_succ_one,add_succ] at k
    exact zero_ne_succ _ k
    rewrite[←mul_pow,h_4,pow_two 2,mul_assoc,
      ←mul_assoc w_2,h_3,mul_comm w,←mul_assoc,h_2]
    exact b2caw
  have cac := MyNat.nameless_2 a b c hc h
  have cpw1w2 : coprime w_1 w_2 := by
    contrapose! v
    rewrite[not_coprime] at v
    cases v
    cases h_5
    cases h_6
    cases h_5
    cases right
    rewrite[hcc,←left,←left_1,←add_mul] at cac
    rewrite[←left,←left_1] at hac
    have lele : w_5≤w_4 := by
      have h := h
      cases le_total w_5 w_4
      exact h_5
      cases h_5
      cases h_6
      rewrite[succ_add,succ_mul,add_mul,add_comm,add_assoc,add_assoc] at hac
      apply add_right_eq_self at hac
      cases a
      rewrite[←not_even] at ho
      exact False.elim (ho zero_is_even)
      rewrite[add_succ,add_succ,eq_comm] at hac
      exact False.elim (zero_ne_succ _ hac)
    cases lele
    rewrite[h_5,add_mul,add_comm] at hac
    apply add_left_cancel at hac
    rewrite[hac] at cac
    contrapose! cac
    rewrite[not_coprime]
    exists w_7,(w_4+w_5),w_6
  have cpw1w2' := MyNat.nameless_1 w_1 w_2 w_3 cpw1w2 u2st
  rewrite[coprime_comm] at cpw1w2
  rewrite[mul_comm] at u2st
  have cpw2w1' := MyNat.nameless_1 w_2 w_1 w_3 cpw1w2 u2st
  cases cpw1w2'
  cases cpw2w1'
  exists w_5,w_4
  rewrite[h_5,h_6]
  constructor
  exact hac
  rewrite[←h_4]
  constructor
  apply squ_inj
  rewrite[mul_pow 2 (2*w_5),mul_pow 2 2,h_6,h_5,mul_pow,u2st,mul_comm,←mul_assoc]
  rfl
  rewrite[add_comm]
  exact hcc
  intro q
  rewrite[eq_comm,two_eq_succ_one] at q
  exact zero_ne_succ 1 q
  intro q
  rewrite[eq_comm,two_eq_succ_one] at q
  exact zero_ne_succ 1 q


Conclusion "
「公理」は基礎であり、それゆえ少し異なるだけでまったく違った結論が得られます。
非ユークリッド幾何学がその例です。
基礎を固めることは重要です。
さて、とうとうその基礎からとある事実を証明する時が来ました。
検討を、祈ります。100行くらいあるこの証明をした君ならできるはずです。
"

-- NewTactic exists
/- Use these commands to add items to the game's inventory. -/

NewTheorem MyNat.nameless_1 MyNat.nameless_2 MyGame.squ_inj
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition even
