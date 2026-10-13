/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorAffine
public import FLT.Mazur.WeierstrassCoefficientShearInitialLineOrigins

/-!
# The two ordered exterior endpoints are the actual conic origins

The full affine comparison identifies both original markings in the final model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hk" => show 0 < start + (0 : Fin (n + 1)).val from by dsimp; omega
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  (hs : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (π ^ start) = 0)
  (h3 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
local notation "hr" => residueTangentEquation_root W
local notation "L" => coefficientShearInitialLine hπ data Q r j hj hs h3 h4 hr
local notation "p" => coefficientShearGluedProjection hπ data Q r j hj
local notation "g" => coefficientShearGluedStructure hπ data Q r j hj
local notation "N" => originalResidueFiniteNormalization hπ data j hj d hk hres

variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)
local notation "F" => coefficientShearResidueExteriorLift hπ data j hj d hk hres a
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "C₀" => coefficientShearInitialConic hπ data Q r j hj hs h3 h4 hr

/-- Zero of the actual ordered exterior is the first initial conic marking. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_zero :
    zero Q ≫ F =
      Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (U).a₁ c hu).toRingHom) ≫ C₀ := by
  rw [← slopeNormalization_first a, infinitySlopeMark, Category.assoc, Category.assoc,
    coefficientShearResidueExteriorLift_affine hπ data j hj hstart hres hs h3 h4 a,
    coefficientShearInitialLine_first]

/-- Infinity of the actual ordered exterior is the opposite initial conic marking. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_infinity :
    infinity Q ≫ F =
      Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (U).a₁ c hu).toRingHom) ≫ C₀ := by
  rw [← slopeNormalization_second a, infinitySlopeMark, Category.assoc, Category.assoc,
    coefficientShearResidueExteriorLift_affine hπ data j hj hstart hres hs h3 h4 a]
  rw [show -(a : Q) = -(U).a₁ from congrArg Neg.neg ha]
  exact coefficientShearInitialLine_second hπ data Q r j hj hs h3 h4 hr hu

end FLT.Mazur.WeierstrassDividedDepth
