/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualRelabel
public import FLT.Mazur.CyclicCharacteristicQuotientCover

/-!
# The retained finite fixed ring is the original quotient coordinate ring

The full residual comparison uses direct pullback invariance, whereas the
existing finite quotient uses inverse pullback to obtain a left group action.
Inversion identifies their actual fixed functions without changing a section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Direct and inverse pullback define the same original finite fixed functions. -/
def affineRelabelCoordinatesEquiv : affineRelabelSections n i ≃+*
    SchemeFiniteGroupQuotient.invariantCoordinates (invariantAffineAction n i) where
  toFun s := ⟨s.val, fun g => s.property g⁻¹⟩
  invFun s := ⟨s.val, fun g => by
    have h := s.property g⁻¹
    change (invariantAffineAction n i g⁻¹⁻¹).hom.appTop s.val = s.val at h
    simpa only [inv_inv] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The coordinate identification preserves the actual regular function. -/
theorem affineRelabelCoordinatesEquiv_val (s : affineRelabelSections n i) :
    (affineRelabelCoordinatesEquiv n i s).val = s.val := rfl

/-- The existing affine quotient is exactly the spectrum of the retained finite fixed ring. -/
def affineRelabelSpectrumIso :
    invariantAffineQuotient n i ≅ Spec (.of (affineRelabelSections n i)) :=
  Scheme.Spec.mapIso (affineRelabelCoordinatesEquiv n i).toCommRingCatIso.op

/-- Transporting the actual finite quotient map gives the direct fixed-ring inclusion. -/
@[reassoc] theorem affineRelabelSpectrumIso_projection :
    invariantAffineQuotientMap n i ≫ (affineRelabelSpectrumIso n i).hom =
      (invariantAffineChart n i).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (affineRelabelSections n i).subtype) := by
  change (_ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [Category.assoc, ← Spec.map_comp]
  rfl

/-- The original finite quotient maps to the full residual invariant spectrum. -/
def affineFiniteToResidualSpectrum :
    invariantAffineQuotient n i ⟶ affineResidualSpectrum n i :=
  (affineRelabelSpectrumIso n i).hom ≫
    Spec.map (CommRingCat.ofHom (affineResidualToRelabel n i))

/-- This comparison factors the original full residual scheme projection exactly. -/
@[reassoc] theorem affineFiniteToResidualSpectrum_projection :
    invariantAffineQuotientMap n i ≫ affineFiniteToResidualSpectrum n i =
      affineResidualProjection n i := by
  rw [affineFiniteToResidualSpectrum, ← Category.assoc,
    affineRelabelSpectrumIso_projection, Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.CyclicCharacteristicOrbit
