/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPartialSmooth
public import FLT.Mazur.WeierstrassDividedVerticalRefinement

/-!
# The horizontal derivative neighborhood of the actual divided chart

The plane presentation proves smoothness after inverting the horizontal
partial even where the vertical derivative vanishes. Pulling this open back
along an arbitrary output constructs a second smooth output neighborhood.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The horizontal partial retains the actual divided equation coefficients. -/
theorem dividedPartial_horizontal :
    dividedPartial W s b3 b4 b6 0 =
      algebraMap R _ W.a₁ * y W s b3 b4 b6 -
        (3 * algebraMap R _ s * x W s b3 b4 b6 ^ 2 +
          2 * algebraMap R _ W.a₂ * x W s b3 b4 b6 + algebraMap R _ b4) := by
  simp [dividedPartial, planeEquation]
  ring

/-- The second plane partial is the already constructed vertical derivative. -/
theorem dividedPartial_vertical :
    dividedPartial W s b3 b4 b6 1 = verticalDerivative W s b3 b4 b6 := by
  rw [verticalDerivative_eq]
  simp [dividedPartial, planeEquation]
  ring

/-- Every point of the derivative open is relatively smooth in the same divided chart. -/
theorem dividedPartial_range_smooth (r : Fin 2) :
    Set.range (PrincipalAffineRefinement.inclusion (dividedPartial W s b3 b4 b6 r)) ⊆
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W s b3 b4 b6)))).smoothLocus := by
  let i := PrincipalAffineRefinement.inclusion (dividedPartial W s b3 b4 b6 r)
  let q := Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6)))
  have hi : i ≫ q = Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away (dividedPartial W s b3 b4 b6 r)))) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  let _ : Smooth (i ≫ q) := by
    rw [hi]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (dividedPartial_smooth W s b3 b4 b6 r))
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq i q
  rw [Scheme.Hom.smoothLocus_eq_top (i ≫ q)] at h
  exact h.ge (Set.mem_univ z)

variable {S : Type u} [CommRing S] [Algebra R S]
  (a : Coordinate W s b3 b4 b6 →ₐ[R] S) (r : Fin 2)
local notation "v" => dividedPartial W s b3 b4 b6 r
local notation "base" => Spec.map (CommRingCat.ofHom
  (algebraMap R (Coordinate W s b3 b4 b6)))

/-- A ring-valued output with invertible derivative lies in the divided smooth locus. -/
theorem dividedPartialUnitPoint_range_smooth (ha : IsUnit (a v)) :
    Set.range (Spec.map (CommRingCat.ofHom a.toRingHom)) ⊆ (base).smoothLocus := by
  let g : Localization.Away v →+* S := IsLocalization.Away.lift _ ha
  have hg : Spec.map (CommRingCat.ofHom g) ≫ PrincipalAffineRefinement.inclusion v =
      Spec.map (CommRingCat.ofHom a.toRingHom) := by
    rw [PrincipalAffineRefinement.inclusion, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsLocalization.Away.lift_comp _ ha)
  rw [← hg]
  rintro _ ⟨z, rfl⟩
  exact dividedPartial_range_smooth W s b3 b4 b6 r
    ⟨Spec.map (CommRingCat.ofHom g) z, rfl⟩

/-- The explicit derivative localization maps entirely into the divided smooth locus. -/
theorem dividedPartialRefinement_range_smooth :
    Set.range (PrincipalAffineRefinement.inclusion (a v) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom)) ⊆ (base).smoothLocus := by
  let j := IsScalarTower.toAlgHom R S (Localization.Away (a v))
  have h := dividedPartialUnitPoint_range_smooth W s b3 b4 b6 (j.comp a) r
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a v)) (a v))
  have he : PrincipalAffineRefinement.inclusion (a v) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom) =
      Spec.map (CommRingCat.ofHom (j.comp a).toRingHom) := by
    rw [PrincipalAffineRefinement.inclusion, ← Spec.map_comp]
    congr 1
  rw [he]
  exact h

end FLT.Mazur.WeierstrassDilatation
