import Game.MyObj.MyNat.Coprime
import Game.MyObj.MyNat.Parity

namespace MyNat

theorem nameless_1 (x y z:ℕ)(h : coprime x y)(i:z^2=x*y) : ∃n,n^2=x := by
  sorry
theorem nameless_2 (x y z:ℕ)(h : coprime x y)(i:x^2+y^2=z^2) : coprime x z := by
  sorry
end MyNat
