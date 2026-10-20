/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Construct a smooth output neighborhood by its vertical derivative

An invertible pulled-back derivative gives a smooth output over an arbitrary
source ring. Localizing at that derivative constructs such a neighborhood.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "v" => verticalDerivative W s b3 b4 b6
local notation "base" => Spec.map (CommRingCat.ofHom
  (algebraMap R (Coordinate W s b3 b4 b6)))

/-- A ring-valued output with invertible derivative lies in the divided smooth locus. -/
theorem dividedUnitPoint_range_smooth (ha : IsUnit (a v)) :
    Set.range (Spec.map (CommRingCat.ofHom a.toRingHom)) ⊆ (base).smoothLocus := by
  let g : Localization.Away v →+* S := IsLocalization.Away.lift _ ha
  have hg : Spec.map (CommRingCat.ofHom g) ≫ PrincipalAffineRefinement.inclusion v =
      Spec.map (CommRingCat.ofHom a.toRingHom) := by
    rw [PrincipalAffineRefinement.inclusion, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsLocalization.Away.lift_comp _ ha)
  rw [← hg]
  rintro _ ⟨z, rfl⟩
  exact verticalDerivative_range_smooth W s b3 b4 b6
    ⟨Spec.map (CommRingCat.ofHom g) z, rfl⟩

/-- The explicit derivative localization maps entirely into the divided smooth locus. -/
theorem dividedVerticalRefinement_range_smooth :
    Set.range (PrincipalAffineRefinement.inclusion (a v) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom)) ⊆ (base).smoothLocus := by
  let j := IsScalarTower.toAlgHom R S (Localization.Away (a v))
  have h := dividedUnitPoint_range_smooth W s b3 b4 b6 (j.comp a)
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a v)) (a v))
  have he : PrincipalAffineRefinement.inclusion (a v) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom) =
      Spec.map (CommRingCat.ofHom (j.comp a).toRingHom) := by
    rw [PrincipalAffineRefinement.inclusion, ← Spec.map_comp]
    congr 1
  rw [he]
  exact h

end FLT.Mazur.WeierstrassDilatation
