import Game.Metadata
import Game.MyObj.MyNat.Function

World "Tutorial"
Level 2

Title "Eq."

namespace MyGame

/--
## 説明
例えば、`X=Y`という形の仮定や定理`h`があった場合、rewrite[h]を使用することで、
ゴール内の**全ての**`X`が`Y`に置き換わります。

## 変種
`rewrite[←h]` : `Y`が`X`になります。

`rewrite[h1,h2]` : `rewrite[h1]`,`rewrite[h2]`を順番に実行します。

`rewrite[h1,h2,h3]` : もちろん3つ以上の置き換えも可能です。

`rewrite[h1] at h2` : **`h2`に対して**`rewrite[h1]`を実行します。

もしかしたら、私が把握できていないだけで他にもあるかも知れません！
-/
TacticDoc rewrite
Introduction "
## 新しいタクティク：`rw`

同じことを表すものってよくありますよね。
例えば、「力」と「パワー」や、「1の次の数」と「2」などがあります。
Lean4で同じことを表すものを置き換えるときは`rw`を使います。
こうすることで、「力」と「パワー」が「力」と「力」になるので、rflが使えます！
"

/--$e$と$mc$が自然数で、$e=mc ^ 2$なら$e=mc ^ 2$。-/
Statement (e mc:ℕ)(h : e = mc ^ 2) : e = mc ^ 2 := by
  Hint "rewrite[h]を使おう。"
  Branch
    rewrite[←h]
    Hint "イースターエッグ発見！ #1"
    rfl
  rewrite[h]
  rfl

Conclusion "いいですね！Lean4では、仮定として用意した等式だけでなく、
すでに分かったこと、「定理」(もしくは「補題」)を番う方法もあります！
詳細はLv4で！\n
ちなみに、`rewrite`より強いTactic`rw`がありますが、
それを使わなかった理由はもちろん、ゲーム性を上げるためです。"
/- Use these commands to add items to the game's inventory. -/

NewTactic rewrite
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
