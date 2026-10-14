/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedChartGeometry
public import FLT.Mazur.EllipticResolvedSmoothPoint

/-!
# Terminal arithmetic charts in the original resolved split fiber

At odd final depth both punctures retain their arithmetic coordinates. At even
final depth the original middle torus retains its reciprocal coordinate.
All maps use the coefficient data constructed from the split-depth hypotheses.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (hk0 : 0 < depth / 2)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D

/-- The positive terminal arithmetic chart in the original final model. -/
def resolvedTerminalPositiveChart (hp : 2 * (depth / 2) < depth) :
    Spec (.of F[T;T⁻¹]) ⟶ resolvedSplitFiber A D :=
  nodeTrivializedPositiveChart A hπ data D r (depth / 2) (le_refl _) (by omega) (by omega)

/-- The negative terminal arithmetic chart in the original final model. -/
def resolvedTerminalNegativeChart (hp : 2 * (depth / 2) < depth) :
    Spec (.of F[T;T⁻¹]) ⟶ resolvedSplitFiber A D :=
  nodeTrivializedNegativeChart A hπ data D r (depth / 2) (le_refl _) (by omega) (by omega)

/-- The middle reciprocal arithmetic chart in the original even final model. -/
def resolvedTerminalMiddleChart (hm : 2 * (depth / 2) = depth) :
    Spec (.of F[T;T⁻¹]) ⟶ resolvedSplitFiber A D :=
  nodeTrivializedMiddleChart A hπ data D r (depth / 2) (le_refl _) (by omega) (by omega)

instance resolvedTerminalPositiveChart_isOpenImmersion (hp : 2 * (depth / 2) < depth) :
    IsOpenImmersion (resolvedTerminalPositiveChart A D r hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (nodeTrivializedPositiveChart ..))

instance resolvedTerminalNegativeChart_isOpenImmersion (hp : 2 * (depth / 2) < depth) :
    IsOpenImmersion (resolvedTerminalNegativeChart A D r hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (nodeTrivializedNegativeChart ..))

instance resolvedTerminalMiddleChart_isOpenImmersion (hm : 2 * (depth / 2) = depth) :
    IsOpenImmersion (resolvedTerminalMiddleChart A D r hk0 hm) :=
  inferInstanceAs (IsOpenImmersion (nodeTrivializedMiddleChart ..))

/-- The positive terminal chart preserves the actual coefficient map. -/
@[reassoc] theorem resolvedTerminalPositiveChart_structure (hp : 2 * (depth / 2) < depth) :
    resolvedTerminalPositiveChart A D r hk0 hp ≫ resolvedSplitStructure A D =
      (MultiplicativeGroupScheme.gm F).hom :=
  nodeTrivializedPositiveChart_structure A hπ data D r (depth / 2) _ _ _

/-- The negative terminal chart preserves the actual coefficient map. -/
@[reassoc] theorem resolvedTerminalNegativeChart_structure (hp : 2 * (depth / 2) < depth) :
    resolvedTerminalNegativeChart A D r hk0 hp ≫ resolvedSplitStructure A D =
      (MultiplicativeGroupScheme.gm F).hom :=
  nodeTrivializedNegativeChart_structure A hπ data D r (depth / 2) _ _ _

/-- The middle terminal chart preserves the actual coefficient map. -/
@[reassoc] theorem resolvedTerminalMiddleChart_structure (hm : 2 * (depth / 2) = depth) :
    resolvedTerminalMiddleChart A D r hk0 hm ≫ resolvedSplitStructure A D =
      (MultiplicativeGroupScheme.gm F).hom :=
  nodeTrivializedMiddleChart_structure A hπ data D r (depth / 2) _ _ _

variable (c₆ : A) (h6 : W.a₆ = π ^ depth * c₆)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = depth / 2)
local notation "pt" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (LaurentUnitPoints.evalUnit (R := F) (nodeTrivializedParameter D c₆ h6 r P))))
local notation "sp" => finitePointSpecialization A hπ data (depth / 2) (le_refl _) P

include hv in
/-- The terminal positive parameter recovers the complete original resolved specialization. -/
theorem resolvedTerminalPositiveChart_specialization (hp : 2 * (depth / 2) < depth)
    (hb : v.b ∈ maximalIdeal A) : pt ≫ resolvedTerminalPositiveChart A D r hk0 hp = sp :=
  finitePointSpecialization_trivialized_positive A hπ data D r (depth / 2) _ _ _ c₆ h6 P v
    (by simpa only [zero_add] using hv) hb

include hv in
/-- The terminal negative parameter recovers the complete original resolved specialization. -/
theorem resolvedTerminalNegativeChart_specialization (hp : 2 * (depth / 2) < depth)
    (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6) (hb : IsUnit v.b) :
    pt ≫ resolvedTerminalNegativeChart A D r hk0 hp = sp :=
  finitePointSpecialization_trivialized_negative A hπ data D r (depth / 2) _ _ _ c₆ h6 P v
    (by simpa only [zero_add] using hv) hr hb

include hv in
/-- The middle parameter recovers the complete original resolved specialization. -/
theorem resolvedTerminalMiddleChart_specialization (hm : 2 * (depth / 2) = depth)
    (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6) :
    pt ≫ resolvedTerminalMiddleChart A D r hk0 hm = sp :=
  finitePointSpecialization_trivialized_middle A hπ data D r (depth / 2) _ _ _ c₆ h6 hr P v
    (by simpa only [zero_add] using hv)

end FLT.Mazur.WeierstrassDividedDepth
