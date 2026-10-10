/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeChartRestriction
public import FLT.Mazur.AffineFreeSheafCoordinates
public import FLT.Mazur.ProjectiveLinearOver

/-!
# Projective transitions of actual finite free sheaf charts

On an affine common refinement, the actual chart transition recovers an
invertible linear map and hence a projective scheme isomorphism over that
refinement's coefficient spectrum. These isomorphisms satisfy the cocycle law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open AffineFreeSheafCoordinates ProjectiveSpace
variable {X : Scheme.{u}} (M : X.Modules)

/-- The actual projective scheme transition recovered from two sheaf charts. -/
def projectiveTransition {U V W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    space Γ(W.toScheme, ⊤) ι ≅ space Γ(W.toScheme, ⊤) κ :=
  linearIso (coordinates W.toScheme (transition M hU hV e d))

/-- A chart's projective self-transition is the identity. -/
lemma projectiveTransition_self {U W : X.Opens} [IsAffine W.toScheme]
    (h : W ≤ U) {ι : Type u} (e : M.restrict U.ι ≅ SheafOfModules.free ι) :
    projectiveTransition M h h e e = Iso.refl _ := by
  rw [projectiveTransition, transition_self, coordinates_refl, linearIso_refl]

/-- Reversing charts inverts their projective transition. -/
lemma projectiveTransition_symm {U V W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    (projectiveTransition M hU hV e d).symm = projectiveTransition M hV hU d e := by
  rw [projectiveTransition, linearIso_symm, ← coordinates_symm, transition_symm]
  rfl

/-- Actual projective transitions satisfy the cocycle law on an affine triple refinement. -/
lemma projectiveTransition_cocycle {U V T W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) (hT : W ≤ T) {ι κ ν : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ)
    (c : M.restrict T.ι ≅ SheafOfModules.free ν) :
    projectiveTransition M hU hV e d ≪≫ projectiveTransition M hV hT d c =
      projectiveTransition M hU hT e c := by
  dsimp only [projectiveTransition]
  rw [linearIso_trans, ← coordinates_trans, transition_cocycle]

/-- Every projective chart transition commutes with its affine coefficient projection. -/
@[reassoc]
lemma projectiveTransition_baseProjection {U V W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    (projectiveTransition M hU hV e d).hom ≫ baseProjection Γ(W.toScheme, ⊤) κ =
      baseProjection Γ(W.toScheme, ⊤) ι :=
  linearIso_baseProjection _

end FLT.Mazur.FiniteFreeChartTransitions
