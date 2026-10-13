/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialInfinityAtlasPullback
public import FLT.Mazur.WeierstrassCoefficientShearInitialLineContraction

/-!
# Both original projections on the full initial infinity slope

The shifted boundary retains the entire initial incidence line in the glued
model, its coefficient structure, and its original integral cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (d).b6
local notation "E" => coefficientShearInitialEquationIso data S r j hj hs h3 h4 hr
local notation "ci" => incidenceCoefficientShearIso W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r
local notation "P" => Localization.Away
  (slopePolynomial a * (Polynomial.X + Polynomial.C r))
local notation "L" => tensorShearInitialInfinitySlopeIso W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r hs h3 h4 hr
local notation "e" => tensorShearNormalEquiv W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r hs h3 h4 hr
local notation "N" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial S) P))
local notation "A" => coefficientShearAtlasMap hπ data S r j hj

local notation "b" => coefficientShearInitialInfinitySlope
  hπ data S r j hj hs h3 h4 hr
local notation "I" => coefficientShearGluedChart hπ data S r j hj (.inl 0)
local notation "L₀" => coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr

/-- The whole shifted slope inclusion agrees in the actual equation gluing. -/
@[reassoc] theorem coefficientShearInitialInfinitySlope_glued :
    b ≫ I = p ≫ L₀ := by
  apply (cancel_mono (coefficientShearGluedIso hπ data S r j hj).hom).mp
  simp only [coefficientShearInitialLine, coefficientShearInitialFiber,
    Category.assoc, coefficientShearGluedIso_chart]
  exact coefficientShearInitialInfinitySlope_comp hπ data S r j hj hs h3 h4 hr

/-- The full original infinity boundary retains its coefficient structure. -/
@[reassoc] theorem coefficientShearInitialInfinitySlope_structure :
    b ≫ coefficientShearAtlasStructure data S r j hj (.inl 0) =
      p ≫ ProjectiveLine.left S ≫ ProjectiveLine.toBase S := by
  rw [← coefficientShearGluedChart_structure hπ,
    coefficientShearInitialInfinitySlope_glued_assoc, coefficientShearInitialLine_structure,
    ProjectiveLine.left_toBase]
  rfl

/-- Every original cubic function on infinity agrees with the full incidence contraction. -/
@[reassoc] theorem coefficientShearInitialInfinitySlope_projection :
    b ≫ TensorOpenChart.projection ≫ WeierstrassIntegralChart.integralCurveChart W 1 =
      p ≫ L₀ ≫ coefficientShearGluedProjection hπ data S r j hj ≫
        finiteGlobalContraction hπ data j hj := by
  rw [← coefficientShearInitialInfinitySlope_glued_assoc,
    coefficientShearGluedChart_projection_assoc]
  change _ = b ≫ finiteInfinityTensorChart hπ data S j hj ≫ _ ≫ _
  rw [finiteInfinityTensorChart_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
