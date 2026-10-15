/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTerminalCyclicCoordinates
public import FLT.Mazur.EllipticMiddleCyclicCoordinates
public import FLT.Mazur.WeierstrassDividedOddCompleteClosedComparison
public import FLT.Mazur.WeierstrassDividedEvenCompleteClosedComparison
public import FLT.Mazur.PolygonPinchingCompleteIdentityCharts

import all FLT.Mazur.WeierstrassDividedOddCompleteClosedComparison
import all FLT.Mazur.WeierstrassDividedEvenCompleteClosedComparison
import all FLT.Mazur.PolygonPinchingCompleteIdentityCharts

/-!
# Original arithmetic terminal coordinates under the full closed comparison

The complete comparison retains the actual positive, negative and middle
arithmetic coordinates with their explicit scales. These equations use the
full comparison that includes every node; no whole-family map is asserted.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonInfinitesimalStages PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeClosedFiberInclusion completePointWeierstrassCurve
  completeIdentityChart completePointIdentityClosedTorus pinchingCompleteClosedIso
  oddCompleteClosedIso evenCompleteClosedIso
attribute [local instance] exactVeroneseProjToBase_lfp
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (r : (ResidueField A)ˣ)
  (s : ℕ) (hs : s + 1 ≤ n) (hstart : start = 0)
local notation "F" => ResidueField A
local notation "a" => nodeLaurentScale D r (start + (s + 1))

section Odd
variable (hp : 2 * (start + s + 1) < depth)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp
local notation "e" => oddCompleteClosedIso hπ data D s hs hstart hp
local notation "c" => exactVeroneseProjToBase F (2 * s + 3) (by omega)

/-- Each original cyclic torus maps to its exact translated complete identity chart. -/
@[reassoc] theorem oddCompleteClosedIso_identityChart (i : Fin (2 * s + 3)) :
    (torusToComponent F).left ≫ (Z i).left ≫ (e).hom ≫ pullback.fst _ _ =
      completePointIdentityClosedTorus F (2 * s + 3) (by omega) 0 ≫
        (completeIdentityChart F (2 * s + 3) (by omega) 0
          (ZMod.finEquiv (2 * s + 3) i)).left ≫ (c).smoothLocus.ι := by
  rw [oddCompleteClosedIso_component]
  have H := congrArg (fun f => f ≫ (c).smoothLocus.ι)
    (completeClosedFiniteChart_zeroIdentityChart F (2 * s + 3) (by omega) i)
  rw [Category.assoc, completeClosedSmoothInclusion_inclusion,
    completeClosedFiniteChart_inclusion_assoc] at H
  simpa only [Over.comp_left, Category.assoc] using H

/-- The full odd comparison sends the actual positive arithmetic torus with its original scale. -/
@[reassoc] theorem oddCompleteClosedIso_arithmeticPositive :
    nodeTrivializedPositiveChart A hπ data D r (s + 1) hs (by omega) (by omega) ≫
        (e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
        completePointIdentityClosedTorus F (2 * s + 3) (by omega) 0 ≫
          (completeIdentityChart F (2 * s + 3) (by omega) 0
            (ZMod.finEquiv (2 * s + 3) ⟨s + 1, by omega⟩)).left ≫ (c).smoothLocus.ι := by
  rw [nodeTrivializedPositiveChart_cyclic A hπ data D r s hs hstart hp]
  simp only [Category.assoc]
  rw [oddCompleteClosedIso_identityChart]

/-- The full odd comparison retains the negative arithmetic coordinate and its signed scale. -/
@[reassoc] theorem oddCompleteClosedIso_arithmeticNegative :
    nodeTrivializedNegativeChart A hπ data D r (s + 1) hs (by omega) (by omega) ≫
        (e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        completePointIdentityClosedTorus F (2 * s + 3) (by omega) 0 ≫
          (completeIdentityChart F (2 * s + 3) (by omega) 0
            (ZMod.finEquiv (2 * s + 3) ⟨s + 2, by omega⟩)).left ≫ (c).smoothLocus.ι := by
  rw [nodeTrivializedNegativeChart_cyclic A hπ data D r s hs hstart hp]
  simp only [Category.assoc]
  rw [oddCompleteClosedIso_identityChart]
end Odd

section Even
variable (hp : 2 * (start + s + 1) = depth)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart (by omega) hp
local notation "e" => evenCompleteClosedIso hπ data D s hs hstart hp
local notation "c" => exactVeroneseProjToBase F (2 * s + 2) (by omega)

/-- Every original even cyclic torus retains its exact complete identity chart label. -/
@[reassoc] theorem evenCompleteClosedIso_identityChart (i : Fin (2 * s + 2)) :
    (torusToComponent F).left ≫ (Z i).left ≫ (e).hom ≫ pullback.fst _ _ =
      completePointIdentityClosedTorus F (2 * s + 2) (by omega) 0 ≫
        (completeIdentityChart F (2 * s + 2) (by omega) 0
          (ZMod.finEquiv (2 * s + 2) i)).left ≫ (c).smoothLocus.ι := by
  rw [evenCompleteClosedIso_component]
  have H := congrArg (fun f => f ≫ (c).smoothLocus.ι)
    (completeClosedFiniteChart_zeroIdentityChart F (2 * s + 2) (by omega) i)
  rw [Category.assoc, completeClosedSmoothInclusion_inclusion,
    completeClosedFiniteChart_inclusion_assoc] at H
  simpa only [Over.comp_left, Category.assoc] using H

/-- The full even comparison retains the arithmetic middle coordinate, including depth two. -/
@[reassoc] theorem evenCompleteClosedIso_arithmeticMiddle :
    nodeTrivializedMiddleChart A hπ data D r (s + 1) hs (by omega) (by omega) ≫
        (e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        completePointIdentityClosedTorus F (2 * s + 2) (by omega) 0 ≫
          (completeIdentityChart F (2 * s + 2) (by omega) 0
            (ZMod.finEquiv (2 * s + 2) ⟨s + 1, by omega⟩)).left ≫ (c).smoothLocus.ι := by
  rw [nodeTrivializedMiddleChart_cyclic A hπ data D s hs hstart hp r]
  simp only [Category.assoc]
  rw [evenCompleteClosedIso_identityChart]
end Even

end FLT.Mazur.WeierstrassDividedDepth
