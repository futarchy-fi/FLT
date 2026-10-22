/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentTensor
public import FLT.Mazur.LaurentPairUnitSections
public import FLT.Mazur.MultiplicativeGroupScheme

/-!
# The double Laurent scheme is the actual torus product

The explicit tensor equivalence identifies both projections and both identity
slices. These formulas let unit-law arguments apply to categorical group laws.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.LaurentPairProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (R : Type u) [CommRing R]
local notation "L" => R[T;T⁻¹]
local notation "D" => R[T;T⁻¹][T;T⁻¹]
local notation "G" => MultiplicativeGroupScheme.gm R

/-- The double Laurent scheme is the categorical product of the original tori. -/
def productIso : Spec (.of D) ≅ ((G) ⊗ (G)).left :=
  Scheme.Spec.mapIso (LaurentTensor.equivalence R L).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R L L).symm

/-- The first projection reads the coefficient Laurent variable. -/
@[reassoc] theorem productIso_fst :
    (productIso R).hom ≫ (fst (G) (G)).left =
      Spec.map (CommRingCat.ofHom (algebraMap L D)) := by
  change Spec.map _ ≫ (pullbackSpecIso R L L).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact LaurentTensor.equivalence_left R L

/-- The second projection reads the outer Laurent variable. -/
@[reassoc] theorem productIso_snd :
    (productIso R).hom ≫ (snd (G) (G)).left =
      Spec.map (CommRingCat.ofHom
        (PolygonScalingNaturality.coeffMap (LaurentPolynomial.C : R →+* L))) := by
  change Spec.map _ ≫ (pullbackSpecIso R L L).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact LaurentTensor.equivalence_right R L

/-- The torus identity is evaluation at the unit Laurent coordinate. -/
theorem identity_left :
    η[(G)].left = PolygonSmoothing.markedTorusSection (1 : Rˣ) := by
  rw [one_spec_asOver_spec_left]
  congr 1
  apply CommRingCat.hom_ext
  change (Bialgebra.counitAlgHom R L).toRingHom =
    (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom
  congr 1
  apply LaurentUnitPoints.hom_ext <;>
    simp [Bialgebra.counitAlgHom_apply, LaurentPolynomial.counit_T,
      LaurentUnitPoints.evalUnit_T]

/-- The first unit slice becomes the categorical left unit input. -/
theorem firstUnit_productIso :
    LaurentPairUnitSections.firstUnit R ≫ (productIso R).hom =
      ((λ_ (G)).inv ≫ η[(G)] ▷ (G)).left := by
  apply pullback.hom_ext
  · change (LaurentPairUnitSections.firstUnit R ≫ (productIso R).hom) ≫
      (fst (G) (G)).left = _
    rw [Category.assoc, productIso_fst, LaurentPairUnitSections.firstUnit_fst]
    change _ = (((λ_ (G)).inv ≫ η[(G)] ▷ (G)) ≫ fst (G) (G)).left
    simp only [Category.assoc, whiskerRight_fst, leftUnitor_inv_fst_assoc,
      Over.comp_left, identity_left]
    rfl
  · change (LaurentPairUnitSections.firstUnit R ≫ (productIso R).hom) ≫
      (snd (G) (G)).left = _
    rw [Category.assoc, productIso_snd, LaurentPairUnitSections.firstUnit_snd]
    change _ = (((λ_ (G)).inv ≫ η[(G)] ▷ (G)) ≫ snd (G) (G)).left
    simp only [Category.assoc, whiskerRight_snd, leftUnitor_inv_snd]
    rfl

/-- The second unit slice becomes the categorical right unit input. -/
theorem secondUnit_productIso :
    LaurentPairUnitSections.secondUnit R ≫ (productIso R).hom =
      ((ρ_ (G)).inv ≫ (G) ◁ η[(G)]).left := by
  apply pullback.hom_ext
  · change (LaurentPairUnitSections.secondUnit R ≫ (productIso R).hom) ≫
      (fst (G) (G)).left = _
    rw [Category.assoc, productIso_fst, LaurentPairUnitSections.secondUnit_fst]
    change _ = (((ρ_ (G)).inv ≫ (G) ◁ η[(G)]) ≫ fst (G) (G)).left
    simp only [Category.assoc, whiskerLeft_fst, rightUnitor_inv_fst]
    rfl
  · change (LaurentPairUnitSections.secondUnit R ≫ (productIso R).hom) ≫
      (snd (G) (G)).left = _
    rw [Category.assoc, productIso_snd, LaurentPairUnitSections.secondUnit_snd]
    change _ = (((ρ_ (G)).inv ≫ (G) ◁ η[(G)]) ≫ snd (G) (G)).left
    simp only [Category.assoc, whiskerLeft_snd, rightUnitor_inv_snd_assoc,
      Over.comp_left, identity_left]
    rfl

end FLT.Mazur.LaurentPairProduct
