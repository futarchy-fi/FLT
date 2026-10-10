/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorInfinity

/-!
# The whole original Y-boundary after coefficient extension

The tensor algebra of the original overlap maps to the finite local model
and the original infinity tensor chart. Both maps retain every original
function, before any decomposition into residue components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart
open scoped TensorProduct
local notation "O" => Overlap W 2 1
local notation "Y" => Coordinate W 1

/-- The original Y-boundary retains its coefficient structure inside the finite model. -/
@[reassoc] theorem finiteYBoundary_structure :
    finiteYBoundary hπ data j hj ≫ finiteStructure hπ data j hj =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [finiteStructure, ← finiteToAffine_toCurve, Category.assoc,
    integralCurveChart_structure, finiteYBoundary_contraction_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

omit [IsDomain R] [IsBezout R] in
/-- The entire original boundary has the same coefficients in the infinity chart. -/
@[reassoc] theorem affineBoundaryToY_structure :
    affineBoundaryToY W ≫ chartStructure W 1 =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [affineBoundaryToY, Category.assoc, ← chartStructure_compatibility]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The full tensor algebra of the original boundary as an open of the finite local model. -/
def finiteTensorYBoundary : Spec (.of (S ⊗[R] O)) ⟶ finiteTensorModel hπ data S j hj :=
  TensorOpenChart.chart _ _ (finiteYBoundary_structure hπ data j hj)

instance finiteTensorYBoundary_isOpenImmersion :
    IsOpenImmersion (finiteTensorYBoundary hπ data S j hj) :=
  inferInstanceAs (IsOpenImmersion (TensorOpenChart.chart _ _ _))

/-- The tensor boundary is the actual pullback of the original integral overlap. -/
theorem finiteTensorYBoundary_isPullback :
    IsPullback (finiteTensorYBoundary hπ data S j hj) TensorOpenChart.projection
      (pullback.snd _ _) (finiteYBoundary hπ data j hj) :=
  TensorOpenChart.chart_isPullback _ _ _

/-- The original boundary's full tensor algebra maps to the infinity tensor algebra. -/
def tensorBoundaryToInfinity : Spec (.of (S ⊗[R] O)) ⟶ Spec (.of (S ⊗[R] Y)) :=
  TensorOpenChart.chart _ _ (affineBoundaryToY_structure (W := W)) ≫
    (pullbackSpecIso R S Y).hom

instance tensorBoundaryToInfinity_isOpenImmersion :
    IsOpenImmersion (tensorBoundaryToInfinity (W := W) S) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

omit [IsDomain R] [IsBezout R] in
/-- Infinity normalization retains the extended coefficients on the whole overlap. -/
@[reassoc] theorem tensorBoundaryToInfinity_structure :
    tensorBoundaryToInfinity (W := W) S ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] Y))) =
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] O))) := by
  rw [tensorBoundaryToInfinity, ← pullbackSpecIso_inv_fst' R S Y,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact TensorOpenChart.chart_fst _ _ _

omit [IsDomain R] [IsBezout R] in
/-- Infinity normalization retains every original localized cubic function. -/
@[reassoc] theorem tensorBoundaryToInfinity_projection :
    tensorBoundaryToInfinity (W := W) S ≫ TensorOpenChart.projection =
      TensorOpenChart.projection ≫ affineBoundaryToY W := by
  change tensorBoundaryToInfinity (W := W) S ≫
    Spec.map (CommRingCat.ofHom _) = _
  rw [tensorBoundaryToInfinity, ← pullbackSpecIso_inv_snd R S Y,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact TensorOpenChart.chart_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
