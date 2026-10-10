/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginAutomorphismAffine
public import FLT.Mazur.WeierstrassChartInjectiveDescent

/-!
# Coordinate pullback of an arbitrary origin-preserving automorphism

Recover the actual algebra automorphism from the restricted scheme isomorphism.
Its action on sections is computed by composition with the original scheme map.
No admissible shape of the two coordinate images is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
  (e : integralCurve W ≅ integralCurve W)
  (hb : e.hom ≫ integralCurveStructure W = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero W)

/-- Pullback on the original affine coordinate algebra, preserving the original coefficients. -/
def originAutCoordinateHom : Coordinate W 2 →ₐ[R] Coordinate W 2 := by
  let f := originAutAffineHom W hΔ e hb hz
  refine { (Spec.preimage f).hom with commutes' := ?_ }
  intro r
  have he : Spec.map (CommRingCat.ofHom
      ((Spec.preimage f).hom.comp (algebraMap R (Coordinate W 2)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2))) := by
    change Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2)) ≫
      Spec.preimage f) = _
    rw [Spec.map_comp, Spec.map_preimage]
    exact originAutAffineHom_base W hΔ e hb hz
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective he)) r

/-- The recovered algebra map represents the whole restricted scheme morphism. -/
theorem originAutCoordinateHom_spec :
    Spec.map (CommRingCat.ofHom (originAutCoordinateHom W hΔ e hb hz).toRingHom) =
      originAutAffineHom W hΔ e hb hz := Spec.map_preimage _

/-- Coordinate pullback is bijective because the original affine restriction is an isomorphism. -/
theorem originAutCoordinateHom_bijective :
    Function.Bijective (originAutCoordinateHom W hΔ e hb hz) := by
  let f := originAutCoordinateHom W hΔ e hb hz
  let g := originAutCoordinateHom W hΔ e.symm
    (originAut_inverse_base W e hb) (originAut_inverse_zero W e hz)
  have hfg : g.comp f = AlgHom.id R (Coordinate W 2) := by
    apply AlgHom.coe_ringHom_injective
    change (CommRingCat.ofHom (g.comp f).toRingHom).hom =
      (CommRingCat.ofHom (RingHom.id (Coordinate W 2))).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom g.toRingHom) = _
    rw [Spec.map_comp, originAutCoordinateHom_spec, originAutCoordinateHom_spec]
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact (originAutAffineIso W hΔ e hb hz).inv_hom_id
  have hgf : f.comp g = AlgHom.id R (Coordinate W 2) := by
    apply AlgHom.coe_ringHom_injective
    change (CommRingCat.ofHom (f.comp g).toRingHom).hom =
      (CommRingCat.ofHom (RingHom.id (Coordinate W 2))).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom f.toRingHom) = _
    rw [Spec.map_comp, originAutCoordinateHom_spec, originAutCoordinateHom_spec]
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact (originAutAffineIso W hΔ e hb hz).hom_inv_id
  exact ⟨Function.LeftInverse.injective (fun x ↦ DFunLike.congr_fun hfg x),
    Function.RightInverse.surjective (fun x ↦ DFunLike.congr_fun hgf x)⟩

/-- The original scheme automorphism induces an actual coefficient-algebra automorphism. -/
def originAutCoordinateEquiv : Coordinate W 2 ≃ₐ[R] Coordinate W 2 :=
  AlgEquiv.ofBijective (originAutCoordinateHom W hΔ e hb hz)
    (originAutCoordinateHom_bijective W hΔ e hb hz)

/-- Pulling a section back through the automorphism is evaluation of its coordinate pullback. -/
theorem originAutCoordinateHom_section {T : Scheme} (q : T ⟶ chartScheme W 2)
    (a : Coordinate W 2) :
    specSectionHom (q ≫ originAutAffineHom W hΔ e hb hz) a =
      specSectionHom q (originAutCoordinateHom W hΔ e hb hz a) := by
  rw [← originAutCoordinateHom_spec, specSectionHom_comp]
  rfl

/-- Fixing an original affine section fixes the values of every pulled-back coordinate function. -/
theorem originAutCoordinateHom_fixed_section {T : Scheme} (q : T ⟶ chartScheme W 2)
    (hq : q ≫ integralCurveChart W 2 ≫ e.hom = q ≫ integralCurveChart W 2)
    (a : Coordinate W 2) :
    specSectionHom q (originAutCoordinateHom W hΔ e hb hz a) = specSectionHom q a := by
  rw [← originAutCoordinateHom_section]
  have he : q ≫ originAutAffineHom W hΔ e hb hz = q := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    rw [Category.assoc, originAutAffineHom_inclusion]
    exact hq
  rw [he]

end FLT.Mazur.WeierstrassIntegralChart
