/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeDualProjectiveTransitions
public import FLT.Mazur.ProjectiveCoefficientFunctor

/-!
# Refinement maps for projective charts of dual coordinates

A smaller affine free chart maps to a larger one by its actual transition
followed by coefficient change. These maps form cartesian refinement squares.
The homogeneous generators are dual to the actual free sheaf coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open ProjectiveSpace
variable {X : Scheme.{u}} (M : X.Modules)

/-- The dual-coordinate projective morphism for an inclusion of affine free charts. -/
def dualChartInclusion {U V : X.Opens} [IsAffine U.toScheme]
    (h : U ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    space Γ(U.toScheme, ⊤) ι ⟶ space Γ(V.toScheme, ⊤) κ :=
  (dualProjectiveTransition M le_rfl h e d).hom ≫ coefficientMap (X.homOfLE h).appTop.hom κ

/-- A chart's refinement to itself is its identity morphism. -/
lemma dualChartInclusion_self {U : X.Opens} [IsAffine U.toScheme] {ι : Type u} [Finite ι]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι) :
    dualChartInclusion M le_rfl e e = 𝟙 _ := by
  simp only [dualChartInclusion, dualProjectiveTransition_self, Iso.refl_hom, Category.id_comp]
  have h : X.homOfLE (show U ≤ U from le_rfl) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    simp
  rw [h, coefficientMap_appTop_id]

/-- Refinement maps compose independently of the intermediate free chart. -/
lemma dualChartInclusion_comp {U V W : X.Opens}
    [IsAffine U.toScheme] [IsAffine V.toScheme]
    (h : U ≤ V) (k : V ≤ W) {ι κ ν : Type u} [Finite ι] [Finite κ] [Finite ν]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ)
    (c : M.restrict W.ι ≅ SheafOfModules.free ν) :
    dualChartInclusion M h e d ≫ dualChartInclusion M k d c =
      dualChartInclusion M (h.trans k) e c := by
  have hr := dualProjectiveTransition_restrict M le_rfl k h d c
  dsimp only [dualChartInclusion]
  simp only [Category.assoc]
  rw [reassoc_of% hr]
  rw [← Category.assoc (dualProjectiveTransition M le_rfl h e d).hom,
    ← Iso.trans_hom, dualProjectiveTransition_cocycle]
  rw [coefficientMap_homOfLE_comp]

/-- Refinement maps commute with the projections onto actual affine opens. -/
@[reassoc]
lemma dualChartInclusion_projection {U V : X.Opens} [IsAffine U.toScheme] [IsAffine V.toScheme]
    (h : U ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    dualChartInclusion M h e d ≫ affineProjection V.toScheme κ =
      affineProjection U.toScheme ι ≫ X.homOfLE h := by
  simp only [dualChartInclusion, Category.assoc, coefficientMap_affineProjection]
  rw [← Category.assoc]
  congr 1
  exact linearIso_affineProjection U.toScheme _

/-- Every refinement square of actual finite projective charts is cartesian. -/
lemma dualChartInclusion_isPullback {U V : X.Opens}
    [IsAffine U.toScheme] [IsAffine V.toScheme] (h : U ≤ V)
    {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    IsPullback (dualChartInclusion M h e d) (affineProjection U.toScheme ι)
      (affineProjection V.toScheme κ) (X.homOfLE h) := by
  apply (affine_isPullback (X.homOfLE h) κ).of_iso
    (dualProjectiveTransition M le_rfl h e d).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [dualChartInclusion]
  · change affineProjection U.toScheme κ =
      (dualProjectiveTransition M le_rfl h e d).inv ≫ affineProjection U.toScheme ι
    rw [Iso.eq_inv_comp]
    exact linearIso_affineProjection U.toScheme _
  · simp
  · simp

/-- Refinement is an open immersion of the actual projective charts. -/
instance dualChartInclusion_isOpenImmersion {U V : X.Opens}
    [IsAffine U.toScheme] [IsAffine V.toScheme] (h : U ≤ V)
    {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    IsOpenImmersion (dualChartInclusion M h e d) :=
  IsOpenImmersion.of_isPullback (dualChartInclusion_isPullback M h e d).flip inferInstance

end FLT.Mazur.FiniteFreeChartTransitions
