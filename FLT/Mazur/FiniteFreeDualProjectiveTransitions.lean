/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeChartProjectiveRestriction
public import FLT.Mazur.FiniteFreeContragredientCoefficients

/-!
# Projective transitions on dual homogeneous generators

The inverse transposes of the actual sheaf coordinate changes define projective
transitions with the dual convention. Pairing preservation, cocycles, and
coefficient squares are inherited from the proved contragredient construction.
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

/-- The projective transition on the dual of the actual free chart coordinates. -/
def dualProjectiveTransition {U V W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    space Γ(W.toScheme, ⊤) ι ≅ space Γ(W.toScheme, ⊤) κ :=
  linearIso (FiniteFreeContragredient.map
    (coordinates W.toScheme (transition M hU hV e d)))

/-- A chart's projective self-transition is the identity. -/
lemma dualProjectiveTransition_self {U W : X.Opens} [IsAffine W.toScheme]
    (h : W ≤ U) {ι : Type u} [Finite ι] (e : M.restrict U.ι ≅ SheafOfModules.free ι) :
    dualProjectiveTransition M h h e e = Iso.refl _ := by
  rw [dualProjectiveTransition, transition_self, coordinates_refl,
    FiniteFreeContragredient.map_refl, linearIso_refl]

/-- Reversing charts inverts their projective transition. -/
lemma dualProjectiveTransition_symm {U V W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    (dualProjectiveTransition M hU hV e d).symm = dualProjectiveTransition M hV hU d e := by
  rw [dualProjectiveTransition, linearIso_symm,
    FiniteFreeContragredient.map_symm, ← coordinates_symm, transition_symm]
  rfl

/-- Actual projective transitions satisfy the cocycle law on an affine triple refinement. -/
lemma dualProjectiveTransition_cocycle {U V T W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) (hT : W ≤ T) {ι κ ν : Type u} [Finite ι] [Finite κ] [Finite ν]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ)
    (c : M.restrict T.ι ≅ SheafOfModules.free ν) :
    dualProjectiveTransition M hU hV e d ≪≫ dualProjectiveTransition M hV hT d c =
      dualProjectiveTransition M hU hT e c := by
  dsimp only [dualProjectiveTransition]
  rw [linearIso_trans, FiniteFreeContragredient.map_trans, ← coordinates_trans, transition_cocycle]

/-- Every projective chart transition commutes with its affine coefficient projection. -/
@[reassoc]
lemma dualProjectiveTransition_baseProjection {U V W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    (dualProjectiveTransition M hU hV e d).hom ≫ baseProjection Γ(W.toScheme, ⊤) κ =
      baseProjection Γ(W.toScheme, ⊤) ι :=
  linearIso_baseProjection _

/-- Dual projective transitions commute with restriction to smaller affine opens. -/
lemma dualProjectiveTransition_restrict {U V W T : X.Opens}
    [IsAffine W.toScheme] [IsAffine T.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) (k : T ≤ W)
    {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    coefficientMap (X.homOfLE k).appTop.hom ι ≫
        (dualProjectiveTransition M hU hV e d).hom =
      (dualProjectiveTransition M (k.trans hU) (k.trans hV) e d).hom ≫
        coefficientMap (X.homOfLE k).appTop.hom κ :=
  FiniteFreeContragredient.projective_coefficient _ _ _
    (transition_coordinates_restrict M hU hV k e d)

end FLT.Mazur.FiniteFreeChartTransitions
