import Game.MyObj.MyNat.Function

def coprime (n m:ℕ) : Prop := ∀(a b d:ℕ),(a*d=n∧b*d=m)→d=1
