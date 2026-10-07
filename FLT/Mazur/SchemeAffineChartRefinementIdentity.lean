/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartReconstruction
public import FLT.Mazur.AffineNamedRefinementReconstruction

/-!
# The effective comparison for identity chart refinement

Faithful reconstruction identifies the constructed comparison with the actual
pullback unit chart, including the spectrum identity transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open SheafPullbackPathComparison SchemePullbackSquare

private theorem cover_identity {T Y : Scheme.{u}} (b : T ⟶ T) (hb : b = 𝟙 T)
    (t : T ⟶ Y) (ht : b ≫ t = t) (M : Y.Modules) :
    (SheafPullbackPathComparison.comparison b t t ht).hom.app M =
      (identityChart b hb ((pullback t).obj M)).hom := by
  subst b
  simpa only [identityChart, identityIso, pullbackCongr, eqToIso_refl,
    Iso.refl_trans, Iso.app_hom] using comparison_id_comp t M

private theorem identity_reconstruction {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : R ⟶ S) (t : Spec S ⟶ Y) {A : (Spec R).Modules} {M : Y.Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M) :
    (AffineRefinementPullback.reconstruction φ φ (𝟙 R) (𝟙 S) (by simp) e).hom ≫
        (SheafPullbackPathComparison.comparison (Spec.map (𝟙 S)) t t (by simp)).hom.app M =
      (pullback (Spec.map φ)).map
          (identityChart (Spec.map (𝟙 R)) (Spec.map_id _) A).hom ≫ e.hom := by
  rw [cover_identity (Spec.map (𝟙 S)) (Spec.map_id _) t (by simp) M]
  exact AffineRefinementPullback.reconstruction_identity φ (𝟙 R) (𝟙 S)
    (Spec.map_id _) (Spec.map_id _) (by simp) e

private theorem named_identity_reconstruction {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : R ⟶ S) (t : Spec S ⟶ Y) {A : (Spec R).Modules} {M : Y.Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ (pullback t).obj M) :
    (AffineNamedRefinementReconstruction.chart φ φ (𝟙 R) (𝟙 S) (by simp)
        t t (by simp) e).hom =
      (pullback (Spec.map φ)).map
          (identityChart (Spec.map (𝟙 R)) (Spec.map_id _) A).hom ≫ e.hom :=
  (AffineNamedRefinementReconstruction.chart_hom φ φ (𝟙 R) (𝟙 S) (by simp)
    t t (by simp) e).trans (identity_reconstruction φ t e)

variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]

/-- The actual pullback unit on the base affine chart. -/
def identityComparison :
    (pullback (Spec.map (Refinement.identity C).base)).obj (C.sheaf D) ≅ C.sheaf D :=
  identityChart (Spec.map (𝟙 C.baseRing)) (Spec.map_id _) (C.sheaf D)

attribute [local irreducible] sheaf reconstruction comparison

/-- Identity refinement reconstructs through the base pullback unit. -/
theorem refinementReconstruction_identity :
    (C.refinementReconstruction C D (Refinement.identity C)).hom =
      (pullback (Spec.map C.ringMap)).map (C.identityComparison D).hom ≫
        (C.reconstruction D).hom := by
  exact named_identity_reconstruction C.ringMap C.cover (C.reconstruction D)

/-- The effective identity-refinement comparison is the pullback unit. -/
theorem comparison_identity :
    C.comparison C D (Refinement.identity C) = C.identityComparison D := by
  apply Iso.ext
  exact (C.comparison_unique C D (Refinement.identity C) (C.identityComparison D).hom
    (C.refinementReconstruction_identity D).symm).symm

end FLT.Mazur.SchemeAffineDescent.Chart
