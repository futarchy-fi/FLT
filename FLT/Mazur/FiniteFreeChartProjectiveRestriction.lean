/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSheafCoordinatePullback
public import FLT.Mazur.FiniteFreeChartProjectiveTransitions

/-!
# Projective chart transitions commute with affine restriction

The actual recovered linear coordinates satisfy the coefficient square on
smaller affine opens. Their projective transitions consequently restrict along
the actual coefficient morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur
namespace AffineFreeSheafCoordinates
open ModuleGlobalEvaluationPullback ProjectiveSpace
variable {X Y : Scheme.{u}}

/-- Pullback and ordinary open restriction give the same free coordinate change. -/
lemma pullbackFreeIso_eq_restrict (f : X ⟶ Y) [IsOpenImmersion f] {ι κ : Type u}
    (e : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ) :
    pullbackFreeIso f e = (freeRestrictIso f ι).symm ≪≫
      (restrictFunctor f).mapIso e ≪≫ freeRestrictIso f κ := by
  apply Iso.ext
  dsimp only [pullbackFreeIso, freeRestrictIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  simp only [Category.assoc]
  rw [← (restrictFunctorIsoPullback f).inv.naturality_assoc]
  simp

variable [IsAffine X] [IsAffine Y]

/-- Recovered coordinates commute with restriction to any smaller affine scheme. -/
lemma coordinates_restrict (f : X ⟶ Y) [IsOpenImmersion f] {ι κ : Type u}
    (e : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ)
    (v : ι →₀ Γ(Y, ⊤)) :
    changeCoefficients f.appTop.hom (coordinates Y e v) =
      coordinates X ((freeRestrictIso f ι).symm ≪≫
        (restrictFunctor f).mapIso e ≪≫ freeRestrictIso f κ)
          (changeCoefficients f.appTop.hom v) := by
  rw [← pullbackFreeIso_eq_restrict]
  exact coordinates_pullback f e v

end AffineFreeSheafCoordinates
namespace FiniteFreeChartTransitions
open AffineFreeSheafCoordinates ProjectiveSpace
variable {X : Scheme.{u}} (M : X.Modules)
attribute [local irreducible] coordinatesIso sectionIso transition refineChart
  ModuleGlobalEvaluationPullback.freeRestrictIso

/-- Actual chart coordinate vectors satisfy the coefficient square on an affine refinement. -/
lemma transition_coordinates_restrict {U V W T : X.Opens}
    [IsAffine W.toScheme] [IsAffine T.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) (k : T ≤ W) {ι κ : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) (v : ι →₀ Γ(W.toScheme, ⊤)) :
    changeCoefficients (X.homOfLE k).appTop.hom
      (coordinates W.toScheme (transition M hU hV e d) v) =
        coordinates T.toScheme (transition M (k.trans hU) (k.trans hV) e d)
          (changeCoefficients (X.homOfLE k).appTop.hom v) := by
  rw [transition_restrict M hU hV k e d]
  exact coordinates_restrict (X.homOfLE k) (transition M hU hV e d) v

/-- The actual projective chart transitions restrict through the coefficient scheme maps. -/
lemma projectiveTransition_restrict {U V W T : X.Opens}
    [IsAffine W.toScheme] [IsAffine T.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) (k : T ≤ W) {ι κ : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    coefficientMap (X.homOfLE k).appTop.hom ι ≫ (projectiveTransition M hU hV e d).hom =
      (projectiveTransition M (k.trans hU) (k.trans hV) e d).hom ≫
        coefficientMap (X.homOfLE k).appTop.hom κ :=
  linearIso_coefficientMap _ _ _ (transition_coordinates_restrict M hU hV k e d)

end FiniteFreeChartTransitions
end FLT.Mazur
