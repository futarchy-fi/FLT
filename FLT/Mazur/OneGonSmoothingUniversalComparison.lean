/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingSmoothParameter
public import FLT.Mazur.OneGonSmoothingCoefficientChange

/-!
# The actual one-gon smoothing is the universal smooth cubic on the overlap

The comparison uses the original integral coefficient morphism and its proved
cartesian square. Both the base projection and the actual infinity section
are retained, rather than just the isomorphism class of a field fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))

/-- The actual coefficient map from the boundary cubic to the smooth universal cubic. -/
def smoothUniversalMorphism : (family t).left ⟶ integralCurve smoothEquation :=
  let _ := (smoothParameter t h₂ ht hf).toAlgebra
  eqToHom (congrArg integralCurve (smoothParameter_equation t h₂ ht hf).symm) ≫
    integralCoefficientMorphism smoothEquation

/-- The original boundary cubic and the universal cubic form a cartesian square. -/
theorem smoothUniversal_isPullback :
    IsPullback (smoothUniversalMorphism t h₂ ht hf) (family t).hom
      (integralCurveStructure smoothEquation)
      (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf))) := by
  let _ := (smoothParameter t h₂ ht hf).toAlgebra
  have h := integralCoefficient_isPullback (S := R) smoothEquation
  refine h.of_iso (eqToIso (congrArg integralCurve
    (smoothParameter_equation t h₂ ht hf))) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp only [Iso.refl_hom, Category.comp_id,
      Category.id_comp]; rfl)
  · simp [smoothUniversalMorphism]
  · simpa only [family, Iso.refl_hom, Category.comp_id, eqToIso.hom,
      RingHom.algebraMap_toAlgebra, Over.mk_hom] using
      (equationTransport_structure (smoothParameter_equation t h₂ ht hf)).symm

/-- The actual infinity marking projects to the universal infinity marking. -/
@[reassoc] theorem smoothUniversalMorphism_marking :
    marking t ≫ smoothUniversalMorphism t h₂ ht hf =
      Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)) ≫
        integralCurveZero smoothEquation := by
  let _ := (smoothParameter t h₂ ht hf).toAlgebra
  change integralCurveZero _ ≫ eqToHom
    (congrArg integralCurve (smoothParameter_equation t h₂ ht hf).symm) ≫ _ = _
  rw [equationTransport_zero_assoc (smoothParameter_equation t h₂ ht hf).symm]
  exact integralCoefficientMorphism_zero (S := R) smoothEquation

/-- The comparison with the original smooth family is an actual pullback isomorphism. -/
def smoothUniversalPullbackIso : (family t).left ≅
    pullback (integralCurveStructure smoothEquation)
      (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf))) :=
  (smoothUniversal_isPullback t h₂ ht hf).isoPullback

/-- The isomorphism retains the actual universal curve projection. -/
@[reassoc] theorem smoothUniversalPullbackIso_fst :
    (smoothUniversalPullbackIso t h₂ ht hf).hom ≫ pullback.fst _ _ =
      smoothUniversalMorphism t h₂ ht hf :=
  (smoothUniversal_isPullback t h₂ ht hf).isoPullback_hom_fst

/-- The isomorphism retains the original boundary parameter projection. -/
@[reassoc] theorem smoothUniversalPullbackIso_snd :
    (smoothUniversalPullbackIso t h₂ ht hf).hom ≫ pullback.snd _ _ = (family t).hom :=
  (smoothUniversal_isPullback t h₂ ht hf).isoPullback_hom_snd

/-- The full marked pullback square retains infinity on both projections. -/
theorem smoothUniversalPullbackIso_marking :
    marking t ≫ (smoothUniversalPullbackIso t h₂ ht hf).hom =
      pullback.lift
        (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)) ≫
          integralCurveZero smoothEquation) (𝟙 _)
        (by simp [Category.assoc, integralCurveZero_structure]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, smoothUniversalPullbackIso_fst,
      smoothUniversalMorphism_marking, pullback.lift_fst]
  · simp only [Category.assoc, smoothUniversalPullbackIso_snd,
      marking_toBase, pullback.lift_snd]

end FLT.Mazur.OneGonSmoothing
