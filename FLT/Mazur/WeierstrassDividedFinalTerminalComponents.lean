/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalComponents
public import FLT.Mazur.WeierstrassDividedTerminalZeroComponents
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins

/-!
# Terminal normalization components with endpoints in the fixed node family

The ordered pair uniformly includes the scale-one case. Each zero endpoint is
its original retained ordered node; both infinity endpoints are the terminal node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R

/-- The ordered full terminal components, constructed from the actual affine charts. -/
def finalTerminalComponent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs :=
  if h : 0 < start + s then
    Fin.cases (terminalFirstComponent hπ data D s hs h hk hp)
      (fun _ => terminalSecondComponent hπ data D s hs h hk hp) i
  else
    Fin.cases (terminalZeroFirstComponent hπ data D s hs (by omega) hk hp)
      (fun _ => terminalZeroSecondComponent hπ data D s hs (by omega) hk hp) i

/-- At positive depth the pair is precisely the original terminal gluing. -/
theorem finalTerminalComponent_positive (h : 0 < start + s) (i : Fin 2) :
    finalTerminalComponent hπ data D s hs hk hp i =
      Fin.cases (terminalFirstComponent hπ data D s hs h hk hp)
        (fun _ => terminalSecondComponent hπ data D s hs h hk hp) i := by
  simp only [finalTerminalComponent, dite_eq_left h]

/-- At scale one the pair is precisely the full zero-depth gluing. -/
theorem finalTerminalComponent_zero_depth (h : start + s = 0) (i : Fin 2) :
    finalTerminalComponent hπ data D s hs hk hp i =
      Fin.cases (terminalZeroFirstComponent hπ data D s hs h hk hp)
        (fun _ => terminalZeroSecondComponent hπ data D s hs h hk hp) i := by
  simp only [finalTerminalComponent, dite_eq_right (show ¬0 < start + s by omega)]

/-- Both zero endpoints keep their original ordered retained node in the fixed family. -/
@[reassoc] theorem finalTerminalComponent_zero (i : Fin 2) :
    ProjectiveLine.zero K ≫ finalTerminalComponent hπ data D s hs hk hp i =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (⟨s, by omega⟩, i))) := by
  change _ = retainedNodeSectionAt hπ data D (s + 1) hs s (by omega) hk i
  rw [retainedNodeSectionAt_original hπ data D s hs 0 hs hk i]
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h,
      orderedRetainedSection_positive hπ data D s hs 0 hs hk h]
    fin_cases i
    · change ProjectiveLine.zero K ≫ terminalFirstComponent hπ data D s hs h hk hp =
        olderGlobalFirstSection hπ data D s hs 0 hs h hk
      rw [ProjectiveLine.zero, Category.assoc, terminalFirstComponent_left,
        ← Category.assoc, conicZeroAffineIso_origin, terminalConicFirstParameter_origin]
    · change ProjectiveLine.zero K ≫ terminalSecondComponent hπ data D s hs h hk hp =
        olderGlobalSecondSection hπ data D s hs 0 hs h hk
      rw [ProjectiveLine.zero, Category.assoc, terminalSecondComponent_left,
        ← Category.assoc, conicZeroAffineIso_origin, terminalConicSecondParameter_origin]
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega),
      orderedRetainedSection_zero hπ data D s hs 0 hs hk (by omega)]
    fin_cases i
    · change ProjectiveLine.zero K ≫ terminalZeroFirstComponent hπ data D s hs (by omega) hk hp =
        olderGlobalZeroFirstSection hπ data D s hs 0 hs (by omega) hk
      rw [ProjectiveLine.zero, Category.assoc, terminalZeroFirstComponent_left,
        ← Category.assoc, conicZeroAffineIso_origin, terminalZeroConicFirstParameter_origin]
    · change ProjectiveLine.zero K ≫ terminalZeroSecondComponent hπ data D s hs (by omega) hk hp =
        olderGlobalZeroSecondSection hπ data D s hs 0 hs (by omega) hk
      rw [ProjectiveLine.zero, Category.assoc, terminalZeroSecondComponent_left,
        ← Category.assoc, conicZeroAffineIso_origin, terminalZeroConicSecondParameter_origin]

/-- Both infinity endpoints are the same original terminal node of the fixed family. -/
@[reassoc] theorem finalTerminalComponent_infinity (i : Fin 2) :
    ProjectiveLine.infinity K ≫ finalTerminalComponent hπ data D s hs hk hp i =
      finalNodeSection hπ data D s hs hk hp (.inr ()) := by
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h]
    fin_cases i
    · exact terminalFirstComponent_infinity hπ data D s hs h hk hp
    · exact terminalSecondComponent_infinity hπ data D s hs h hk hp
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    fin_cases i
    · exact terminalZeroFirstComponent_infinity hπ data D s hs (by omega) hk hp
    · exact terminalZeroSecondComponent_infinity hπ data D s hs (by omega) hk hp

end FLT.Mazur.WeierstrassDividedDepth
