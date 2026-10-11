/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingUniversalComparison
public import FLT.Mazur.WeierstrassCoefficientGroup
public import FLT.Mazur.WeierstrassOriginIsomorphismGroup

/-!
# The original smooth one-gon boundary as a group scheme

The existing integral cubic group law is used on the original boundary equation.
Its comparison with the universal smooth family is the original Cartesian map,
now retaining the entire commutative group object.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))

/-- The original smooth boundary cubic with its already proved group law. -/
def smoothGroup : CommGrp (Over (Spec (.of R))) :=
  integralCurveGroup (equation t) (smooth_discriminant t ht hf)

/-- Forgetting the group law gives the unchanged original boundary family. -/
theorem smoothGroup_carrier : (smoothGroup t ht hf).X = family t := rfl

/-- The universal group pulled back along the original boundary coefficient point. -/
def smoothUniversalGroup : CommGrp (Over (Spec (.of R))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)))).mapCommGrp.obj
    (integralCurveGroup smoothEquation smoothEquation_discriminant)

/-- Equation equality identifies the already constructed group objects. -/
def equationGroupIso {W V : WeierstrassCurve R} (h : W = V)
    (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    integralCurveGroup W hW ≅ integralCurveGroup V hV :=
  originIsoGroupIso W V hW hV (eqToIso (congrArg integralCurve h))
    (equationTransport_structure h) (equationTransport_zero h)

/-- Equation equality transport retains its actual morphism of original cubics. -/
theorem equationGroupIso_hom {W V : WeierstrassCurve R} (h : W = V)
    (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    (equationGroupIso h hW hV).hom.hom.hom.hom.left =
      eqToHom (congrArg integralCurve h) := rfl

/-- The original boundary comparison preserves the constructed group operations. -/
def smoothUniversalGroupIso : smoothGroup t ht hf ≅ smoothUniversalGroup t h₂ ht hf := by
  letI := (smoothParameter t h₂ ht hf).toAlgebra
  have hd : IsUnit (smoothEquation.map (algebraMap ParameterRing R)).Δ :=
    (smoothParameter_equation t h₂ ht hf).symm ▸ smooth_discriminant t ht hf
  exact equationGroupIso (smoothParameter_equation t h₂ ht hf).symm
    (smooth_discriminant t ht hf) hd ≪≫
      integralCurveCoefficientGroupIso smoothEquation smoothEquation_discriminant hd

/-- The group comparison retains exactly the original map to the universal cubic. -/
@[reassoc] theorem smoothUniversalGroupIso_fst :
    (smoothUniversalGroupIso t h₂ ht hf).hom.hom.hom.hom.left ≫ pullback.fst _ _ =
      smoothUniversalMorphism t h₂ ht hf := by
  let _ := (smoothParameter t h₂ ht hf).toAlgebra
  change ((equationGroupIso (smoothParameter_equation t h₂ ht hf).symm _ _).hom.hom.hom.hom.left
    ≫ (integralCurveCoefficientGroupIso smoothEquation _ _).hom.hom.hom.hom.left) ≫ _ = _
  rw [equationGroupIso_hom, integralCurveCoefficientGroupIso_hom, Category.assoc]
  exact congrArg
    (fun k => eqToHom (congrArg integralCurve (smoothParameter_equation t h₂ ht hf).symm) ≫ k)
    (integralCurveCoefficientBaseChangeIso_fst (S := R) smoothEquation)

/-- Forgetting the group comparison recovers the previously constructed family comparison. -/
theorem smoothUniversalGroupIso_hom :
    (smoothUniversalGroupIso t h₂ ht hf).hom.hom.hom.hom.left =
      (smoothUniversalPullbackIso t h₂ ht hf).hom := by
  apply pullback.hom_ext
  · exact (smoothUniversalGroupIso_fst t h₂ ht hf).trans
      (smoothUniversalPullbackIso_fst t h₂ ht hf).symm
  · exact (smoothUniversalGroupIso t h₂ ht hf).hom.hom.hom.hom.w.trans
      (smoothUniversalPullbackIso_snd t h₂ ht hf).symm

end FLT.Mazur.OneGonSmoothing
