-- from https://github.com/leanprover-community/NNG4/blob/main/Game/Tactic/Cases.lean
-- Modified
import Game.MyObj.MyNat.MyNat
import Mathlib.Tactic.Cases

/-!
# Modified `cases` tactic

Modify `cases` tactic to always show `(0 : MyNat)` instead of `MyNat.zero` and
to support the lean3-style `with` keyword.

This is mainly copied and modified from the mathlib-tactic `cases'`.
-/

namespace MyGame

/-- Modified `casesOn` principal to use `0` instead of `MyNat.zero`. -/
def casesOn' {P : ℕ → Sort u} (t : ℕ) (zero : P 0)
    (succ : (a : ℕ) → P (a′)) : P t := by
  cases t with
  | zero => assumption
  | succ n => apply succ

open Lean Meta Elab Parser Tactic Mathlib.Tactic
open private getElimNameInfo from Lean.Elab.Tactic.Induction

/-- このゲームのために変更された `cases` 。

使用法:;
1.`n : ℕ` があるときに `cases n with d`;
2.`h : P ∨ Q`があるときに`cases h with h1 h2`;
3.`h : a ≤ b`があるときに`cases h with c hc`

*(This implementation mimics the `cases'` from mathlib. The actual `cases` tactic in mathlib has a more complex syntax)*
-/
elab (name := cases) "cases " tgts:(Parser.Tactic.casesTarget,+) usingArg:((" using " ident)?)
    withArg:((" with" (ppSpace colGt binderIdent)+)?) : tactic => do
  let (targets, toTag) ← elabCasesTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := false)

    -- Edit: If `MyGame.casesOn` is used, we want to use `MyGame.casesOn` instead.
    let elimInfo ← match elimInfo.elimExpr.getAppFn.constName? with
    | some `MyNat.casesOn =>
      let modifiedUsingArgs : TSyntax Name.anonymous := ⟨
        match usingArg.raw with
        | .node info kind #[] =>
          -- TODO: How do you construct syntax in a semi-userfriendly way??
          .node info kind #[.atom info "using", .ident info "MyGame.casesOn'".toSubstring `MyGame.casesOn' []]
        | other => other ⟩
      let newElimInfo ← getElimNameInfo modifiedUsingArgs targets (induction := false)
      pure newElimInfo
    | _ => pure elimInfo

    let targets ← addImplicitTargets elimInfo targets
    let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·]!)
    let motive := elimArgs[elimInfo.motivePos]!
    let g ← generalizeTargetsEq g (← inferType motive) targets
    let (targetsNew, g) ← g.introN targets.size
    g.withContext do
      ElimApp.setMotiveArg g motive.mvarId! targetsNew
      g.assign result.elimApp
      let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
         (numEqs := targets.size) (toClear := targetsNew) (toTag := toTag)
      setGoals <| subgoals.toList ++ gs



end MyGame
