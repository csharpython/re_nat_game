import Game.Metadata
import Game.Levels.Tutorial
import Game.Levels.Add
import Game.MyObj.MyNat.Le

World "Le"
Level 4

Title "つながる　つなげる(le_trans)"

namespace MyGame

Introduction "
  想いはきっと、未来へつながる。
## `cases`
新しいtactic `cases`が利用可能になりました。
このtacticは、∃を含む仮定に対して効果的です。(他にも何か?)
"

/--
## 使用法1 : 0 or not
`n : ℕ` があるときにゴール`P n`に対して`cases n with d`を使うと、ゴールが`P 0`と`P (d‘)`になる。

## 使用法2 : 場合分け
`h : P ∨ Q`があるときに`cases h with h1 h2`を使うと、`P`である場合のゴールと`Q`である場合のゴールが作られる。`h`は消える。

## 使用法3 : ≤
`h : a ≤ b`があるときに`cases h with c hc`を使うと、`h`が`hc : b = a + c`に変化する。

-/
TacticDoc cases

NewTactic cases
TheoremTab "≤"

/--
## 説明
$a,b,c$を自然数とする。$a≤b∧b≤c$なら$a≤c$である。
-/
TheoremDoc MyGame.le_trans as "le_trans" in "≤"

/--$∀\{a,b,c\}∈ℕ³,a ≤ b∧b ≤ c → a ≤ c$-/
Statement le_trans (a b c:ℕ)(h1 : a ≤ b)(h2 : b ≤ c) : a ≤ c := by
  cases h1
  cases h2
  exists w_1+w
  rewrite[h_1,h,add_comm w_1,add_assoc]
  rfl

Conclusion "
不等号の世界へようこそ。
"
/- Use these commands to add items to the game's inventory. -/

-- NewTactic induction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
