/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIsomorphismAffine
public import FLT.Mazur.WeierstrassChartInjectiveDescent

/-!
# Coordinate pullback between distinct smooth cubics

Recover the coefficient-algebra equivalence from an arbitrary actual
origin-preserving scheme isomorphism, without assuming admissible coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R) (hV : IsUnit V.Δ)
  (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

/-- The actual coefficient-preserving pullback from target to source affine coordinates. -/
def originIsoCoordinateHom : Coordinate V 2 →ₐ[R] Coordinate W 2 := by
  let f := originIsoAffineHom W V hV e hb hz
  refine { (Spec.preimage f).hom with commutes' := ?_ }
  intro r
  have he : Spec.map (CommRingCat.ofHom
      ((Spec.preimage f).hom.comp (algebraMap R (Coordinate V 2)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2))) := by
    change Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate V 2)) ≫
      Spec.preimage f) = _
    rw [Spec.map_comp, Spec.map_preimage]
    exact originIsoAffineHom_base W V hV e hb hz
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective he)) r

/-- The recovered ring map represents the whole restricted scheme morphism. -/
theorem originIsoCoordinateHom_spec :
    Spec.map (CommRingCat.ofHom (originIsoCoordinateHom W V hV e hb hz).toRingHom) =
      originIsoAffineHom W V hV e hb hz := Spec.map_preimage _

/-- The coordinate pullback is bijective, since the original scheme map is an isomorphism. -/
theorem originIsoCoordinateHom_bijective (hW : IsUnit W.Δ) :
    Function.Bijective (originIsoCoordinateHom W V hV e hb hz) := by
  let f := originIsoCoordinateHom W V hV e hb hz
  let g := originIsoCoordinateHom V W hW e.symm
    (originIso_inverse_base W V e hb) (originIso_inverse_zero W V e hz)
  have hfg : g.comp f = AlgHom.id R (Coordinate V 2) := by
    apply AlgHom.coe_ringHom_injective
    change (CommRingCat.ofHom (g.comp f).toRingHom).hom =
      (CommRingCat.ofHom (RingHom.id (Coordinate V 2))).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom g.toRingHom) = _
    rw [Spec.map_comp, originIsoCoordinateHom_spec, originIsoCoordinateHom_spec]
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact (originIsoAffineIso W V hV e hb hz hW).inv_hom_id
  have hgf : f.comp g = AlgHom.id R (Coordinate W 2) := by
    apply AlgHom.coe_ringHom_injective
    change (CommRingCat.ofHom (f.comp g).toRingHom).hom =
      (CommRingCat.ofHom (RingHom.id (Coordinate W 2))).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom f.toRingHom) = _
    rw [Spec.map_comp, originIsoCoordinateHom_spec, originIsoCoordinateHom_spec]
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact (originIsoAffineIso W V hV e hb hz hW).hom_inv_id
  exact ⟨Function.LeftInverse.injective (fun x => DFunLike.congr_fun hfg x),
    Function.RightInverse.surjective (fun x => DFunLike.congr_fun hgf x)⟩

/-- The original scheme isomorphism yields an actual coefficient-algebra equivalence. -/
def originIsoCoordinateEquiv (hW : IsUnit W.Δ) : Coordinate V 2 ≃ₐ[R] Coordinate W 2 :=
  AlgEquiv.ofBijective (originIsoCoordinateHom W V hV e hb hz)
    (originIsoCoordinateHom_bijective W V hV e hb hz hW)

/-- Pullback of a section agrees with the actual coordinate pullback. -/
theorem originIsoCoordinateHom_section {T : Scheme} (q : T ⟶ chartScheme W 2)
    (a : Coordinate V 2) :
    specSectionHom (q ≫ originIsoAffineHom W V hV e hb hz) a =
      specSectionHom q (originIsoCoordinateHom W V hV e hb hz a) := by
  rw [← originIsoCoordinateHom_spec, specSectionHom_comp]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
