/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityFactorRatioParameter
public import FLT.Mazur.WeierstrassSplitNodalLaurent
public import FLT.Mazur.NodalFiberZeroTangentMobiusPuncture

/-!
# The full split nodal infinity factor ratio is a torus isomorphism

Over an arbitrary coefficient ring, the original regular infinity ratio is
exactly the inverse of the ordered tangent unit. Its inverse is supplied
by the explicit Laurent equivalence of the full cubic chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (a : Rˣ) (s : R)
local notation "W" => splitNodalEquation a
/-- The exact full regular unit on the split nodal infinity chart. -/
def splitNodalRegularInfinityUnit : (Coordinate W 1)ˣ :=
  infinityFactorRatioUnit W ⊥ (by exact ⟨1, by simp⟩) (by simp [splitNodalEquation])
    (by simp [splitNodalEquation]) (by simp [splitNodalEquation])
    (by simp [splitNodalEquation]) s 0 0 (by simp) (by simp)

/-- The original regular infinity parameter, with zero coefficient ideal and root. -/
def splitNodalRegularInfinityParameter :
    Spec (.of (Coordinate W 1)) ⟶ PolygonSmoothing.branchTorus R :=
  infinityFactorRatioParameter W ⊥ (by exact ⟨1, by simp⟩) (by simp [splitNodalEquation])
    (by simp [splitNodalEquation]) (by simp [splitNodalEquation])
    (by simp [splitNodalEquation]) s 0 0 (by simp) (by simp)

local notation "U" => splitNodalRegularInfinityUnit a s
local notation "P" => splitNodalRegularInfinityParameter a s

/-- At the full split nodal chart the exact factor ratio is the inverse tangent unit. -/
theorem splitNodalInfinityFactorRatioUnit : U = (splitNodalTangentUnit a)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  apply Units.ext
  have h := infinityFactorRatioUnit_denominator W ⊥ (by exact ⟨1, by simp⟩)
    (by simp [splitNodalEquation])
    (by simp [splitNodalEquation]) (by simp [splitNodalEquation])
    (by simp [splitNodalEquation]) s 0 0 (by simp) (by simp)
  simp only [infinityOppositeFactor, infinitySmallFactor, Polynomial.eval₂_zero,
    zero_add, map_zero, zero_mul, add_zero, mul_zero, sub_zero] at h
  change (U : Coordinate W 1) *
    (1 + coord W 1 0 * algebraMap R (Coordinate W 1) (a : R)) = 1 at h
  change (U : Coordinate W 1) *
    (1 + algebraMap R (Coordinate W 1) (a : R) * coord W 1 0) = 1
  rw [mul_comm (coord W 1 0)] at h
  exact h

/-- The original full infinity chart is the torus with its reciprocal factor-ratio coordinate. -/
def splitNodalInfinityFactorRatioIso :
    Spec (.of (Coordinate W 1)) ≅ PolygonSmoothing.branchTorus R :=
  (Scheme.Spec.mapIso (splitNodalChartLaurentEquiv a).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    PolygonSmoothing.edgeInversion R

/-- The explicit torus isomorphism agrees with the complete original regular ratio. -/
theorem splitNodalInfinityFactorRatioIso_hom :
    (splitNodalInfinityFactorRatioIso a).hom = P := by
  unfold splitNodalRegularInfinityParameter infinityFactorRatioParameter
  change _ = Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit U).toRingHom)
  rw [splitNodalInfinityFactorRatioUnit, NodalFiber.unitParameter_inverse]
  rfl

/-- The full original factor ratio is an isomorphism, over a possibly nonreduced base. -/
instance splitNodalInfinityFactorRatioParameter_isIso : IsIso P := by
  rw [← splitNodalInfinityFactorRatioIso_hom]
  infer_instance

/-- The actual regular ratio reaches every point of the torus. -/
theorem splitNodalInfinityFactorRatioParameter_surjective : Function.Surjective P := by
  rw [← splitNodalInfinityFactorRatioIso_hom]
  exact (Scheme.homeoOfIso (splitNodalInfinityFactorRatioIso a)).surjective

variable (V : WeierstrassCurve R) (ha : IsUnit V.a₁)
  (I : Ideal R) (hI : IsNilpotent I) (hzero : I = ⊥)
  (h2 : V.a₂ ∈ I) (h3 : V.a₃ ∈ I) (h4 : V.a₄ ∈ I) (h6 : V.a₆ ∈ I)
  (b3 : R) (r : Polynomial R) (hr : r ∈ I.map Polynomial.C) (hb : b3 ∈ I)

include ha hzero in
/-- A vanishing coefficient ideal identifies the entire original ratio with the split one. -/
theorem infinityFactorRatioParameter_isIso_of_ideal_zero :
    IsIso (infinityFactorRatioParameter V I hI h2 h3 h4 h6 s b3 r hr hb) := by
  subst I
  have hr0 : r = 0 := by simpa using hr
  have hb0 : b3 = 0 := by simpa using hb
  subst r b3
  have hV : V = splitNodalEquation ha.unit := by
    ext
    · exact ha.unit_spec.symm
    · exact (Ideal.mem_bot.mp h2)
    · exact (Ideal.mem_bot.mp h3)
    · exact (Ideal.mem_bot.mp h4)
    · exact (Ideal.mem_bot.mp h6)
  generalize ha.unit = tangent at hV
  subst V
  exact splitNodalInfinityFactorRatioParameter_isIso tangent s

end FLT.Mazur.WeierstrassIntegralChart
