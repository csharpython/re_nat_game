import Game.MyObj.MyNat.Function

def even (n:ℕ) : Prop := ∃(m:ℕ),(m*2)=n
def odd (n:ℕ) : Prop := ∃(m:ℕ),(m*2+1)=n
