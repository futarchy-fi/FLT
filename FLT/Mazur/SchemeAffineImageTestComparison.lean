/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineAmbientTestRefinement
public import FLT.Mazur.ModuleSheafLocalHomComposition

/-!
# Image-open restrictions of the glued comparisons

The actual comparisons of ambient chart sheaves induce invertible maps on
image opens. Their cocycle and refinement laws hold on every smaller subopen.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open ModuleSheafOpenImmersionLocalHom ModuleSheafMorphismGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W Z : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [IsOpenImmersion C.base] [IsOpenImmersion C'.base]
attribute [local irreducible] sheaf ambientTestComparison

/-- The glued comparison on the image open of a common test. -/
def imageTestComparison (a : W ⟶ X) [IsOpenImmersion a]
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a) :
    ((pushforward C.base).obj (C.sheaf D)).over a.opensRange ⟶
      ((pushforward C'.base).obj (C'.sheaf D)).over a.opensRange :=
  localHom a (C.ambientTestComparison C' D a i j hi hj)

/-- The induced image-open map is invertible. -/
instance imageTestComparison_isIso (a : W ⟶ X) [IsOpenImmersion a]
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a) :
    IsIso (C.imageTestComparison C' D a i j hi hj) := by
  unfold imageTestComparison
  infer_instance

/-- The global cocycle restricts to every subopen of a common image. -/
theorem imageTestComparison_cocycle (T : Fin 3 → Chart p)
    (a : W ⟶ X) [IsOpenImmersion a] (b : ∀ i, W ⟶ Spec (T i).baseRing)
    (h : ∀ i, b i ≫ (T i).base = a)
    [∀ i, ((pullback (T i).cover).obj M).IsQuasicoherent]
    [∀ i, IsOpenImmersion (T i).base]
    (U : X.Opens) (hU : U ≤ a.opensRange)
    (s : Γ((pushforward (T 0).base).obj ((T 0).sheaf D), U)) :
    localApp ((T 1).imageTestComparison (T 2) D a (b 1) (b 2) (h 1) (h 2)) hU
        (localApp ((T 0).imageTestComparison (T 1) D a (b 0) (b 1) (h 0) (h 1)) hU s) =
      localApp ((T 0).imageTestComparison (T 2) D a (b 0) (b 2) (h 0) (h 2)) hU s :=
  localHom_cocycle_app a _ _ _ (ambientTestComparison_cocycle D T a b h) U hU s

/-- Refining a common open test restricts its comparison on all smaller subopens. -/
theorem imageTestComparison_refine (t : Z ⟶ W) (a : W ⟶ X)
    [IsOpenImmersion t] [IsOpenImmersion a]
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a)
    (U : X.Opens) (hU : U ≤ (t ≫ a).opensRange) (hA : U ≤ a.opensRange) :
    localApp (C.imageTestComparison C' D (t ≫ a) (t ≫ i) (t ≫ j)
        (by rw [Category.assoc, hi]) (by rw [Category.assoc, hj])) hU =
      localApp (C.imageTestComparison C' D a i j hi hj) hA := by
  apply localHom_refine_of_eq a t (t ≫ a) rfl
  simpa only [AffineIteratedPullbackSections.compositeIso, pullbackCongr,
    eqToIso_refl, Iso.trans_hom, Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] using C.ambientTestComparison_refine C' D t a i j hi hj

end FLT.Mazur.SchemeAffineDescent.Chart
