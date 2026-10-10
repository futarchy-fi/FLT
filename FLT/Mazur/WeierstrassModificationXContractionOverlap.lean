/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLocalization
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# The actual overlap preserves contraction to the original cubic

The principal-open isomorphism glues the two existing contraction maps: both
recover the same original horizontal and vertical coordinates. The open
immersions and the comparison are actual scheme morphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The inverse incidence coordinate recovers the original horizontal coordinate. -/
theorem mapped_scale_inverse {S : Type u} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) (a : Sˣ)
    (ha : f (t W s b3 b4 b6) = a) :
    algebraMap R S s * (↑a⁻¹ : S) = f (x W s b3 b4 b6) := by
  have h := congrArg f (incidence W s b3 b4 b6)
  simp only [map_mul, AlgHom.commutes, ha] at h
  rw [← h, mul_right_comm, Units.mul_inv, one_mul]

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The generic overlap substitution preserves the original affine contraction. -/
theorem dividedOverlapMap_fromOriginal {S : Type u} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) (a : Sˣ)
    (ha : f (t W s b3 b4 b6) = a) :
    (dividedOverlapMap W s b3 b4 b6 f a ha).comp
        (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6) =
      f.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, AlgHom.comp_apply, WeierstrassDilatation.fromOriginal_x, map_mul,
      AlgHom.commutes, dividedOverlapMap_x, fromOriginal_x]
    exact mapped_scale_inverse W s b3 b4 b6 f a ha
  · simp only [Fin.mk_one, AlgHom.comp_apply, WeierstrassDilatation.fromOriginal_y, map_mul,
      AlgHom.commutes, dividedOverlapMap_y, fromOriginal_y, y]
    rw [← mul_assoc, mapped_scale_inverse W s b3 b4 b6 f a ha]
  · simp [WeierstrassIntegralChart.coord_self]

/-- Inclusion of the incidence principal open into its actual x-direction chart. -/
def xOpenInclusion : Spec (.of (XOpen W s b3 b4 b6)) ⟶
    Spec (.of (Coordinate W s b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Coordinate W s b3 b4 b6) _))

/-- Inclusion of the divided principal open into its actual divided chart. -/
def dividedOpenInclusion : Spec (.of (DividedOpen W s b3 b4 b6)) ⟶
    Spec (.of (WeierstrassDilatation.Coordinate W s b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (WeierstrassDilatation.Coordinate W s b3 b4 b6) _))

instance xOpenInclusion_isOpenImmersion : IsOpenImmersion (xOpenInclusion W s b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (t W s b3 b4 b6)

instance dividedOpenInclusion_isOpenImmersion :
    IsOpenImmersion (dividedOpenInclusion W s b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (WeierstrassDilatation.x W s b3 b4 b6)

/-- The actual principal opens of the two charts are isomorphic over the original base. -/
def overlapIso : Spec (.of (XOpen W s b3 b4 b6)) ≅
    Spec (.of (DividedOpen W s b3 b4 b6)) :=
  Scheme.Spec.mapIso (overlapEquiv W s b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- Both contractions agree on the actual open overlap, so they can be glued. -/
theorem overlapIso_toCurve :
    (overlapIso W s b3 b4 b6).hom ≫ dividedOpenInclusion W s b3 b4 b6 ≫
        WeierstrassDilatation.toCurve W s b3 b4 b6 h3 h4 h6 =
      xOpenInclusion W s b3 b4 b6 ≫ toCurve W s b3 b4 b6 h3 h4 h6 := by
  have he : (overlapForward W s b3 b4 b6).comp
      ((IsScalarTower.toAlgHom R _ (DividedOpen W s b3 b4 b6)).comp
        (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6)) =
      (IsScalarTower.toAlgHom R _ (XOpen W s b3 b4 b6)).comp
        (fromOriginal W s b3 b4 b6 h3 h4 h6) := by
    have hh := dividedOverlapMap_fromOriginal W s b3 b4 b6 h3 h4 h6
      (IsScalarTower.toAlgHom R _ (XOpen W s b3 b4 b6))
      (xOpenUnit W s b3 b4 b6) (xOpenUnit_val W s b3 b4 b6).symm
    apply AlgHom.ext
    intro z
    change overlapForward W s b3 b4 b6 (algebraMap _ _
      (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6 z)) = _
    rw [overlapForward_base]
    exact AlgHom.congr_fun hh z
  have hr := congrArg (fun f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R]
    XOpen W s b3 b4 b6 => CommRingCat.ofHom f.toRingHom) he
  change Spec.map _ ≫ Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ (Spec.map _ ≫ _)
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 1
  exact congrArg Spec.map hr

end FLT.Mazur.WeierstrassModificationX
