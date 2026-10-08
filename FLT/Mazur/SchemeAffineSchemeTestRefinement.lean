/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSchemeTestComparison

/-!
# Refinement of scheme-test comparisons

The normalized glued comparison is independent of a presentation of its pair
map and commutes with further pullback along any scheme morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W Z : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] sheaf CrossRefinement.effectiveComparison baseOverlapComparison

/-- Any pair map with the prescribed projections yields the same test comparison. -/
theorem normalizedOverlapMap_eq_schemeTestComparison (c : W ⟶ C.baseOverlap C')
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : c ≫ Limits.pullback.fst C.base C'.base = i)
    (hj : c ≫ Limits.pullback.snd C.base C'.base = j)
    (w : i ≫ C.base = j ≫ C'.base) :
    C.normalizedOverlapMap C' D c i j hi hj = C.schemeTestComparison C' D i j w := by
  have hc : c = Limits.pullback.lift i j w := by
    apply Limits.pullback.hom_ext
    · simpa only [Limits.pullback.lift_fst] using hi
    · simpa only [Limits.pullback.lift_snd] using hj
  subst c
  rfl

/-- Scheme-test comparison commutes with arbitrary further pullback. -/
theorem schemeTestComparison_refine (t : Z ⟶ W)
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (w : i ≫ C.base = j ≫ C'.base) :
    (pullback t).map (C.schemeTestComparison C' D i j w) ≫
        (pullbackComp t j).hom.app (C'.sheaf D) =
      (pullbackComp t i).hom.app (C.sheaf D) ≫
        C.schemeTestComparison C' D (t ≫ i) (t ≫ j)
          (by simpa only [Category.assoc] using congrArg (t ≫ ·) w) := by
  have hi : (t ≫ Limits.pullback.lift i j w) ≫ Limits.pullback.fst C.base C'.base =
      t ≫ i := by rw [Category.assoc, Limits.pullback.lift_fst]
  have hj : (t ≫ Limits.pullback.lift i j w) ≫ Limits.pullback.snd C.base C'.base =
      t ≫ j := by rw [Category.assoc, Limits.pullback.lift_snd]
  have hn := SheafPullbackMapNormalization.normalize_refine
    (Limits.pullback.lift i j w) (Limits.pullback.fst C.base C'.base)
    (Limits.pullback.snd C.base C'.base) i j
    (Limits.pullback.lift_fst i j w) (Limits.pullback.lift_snd i j w)
    t (t ≫ Limits.pullback.lift i j w) rfl (t ≫ i) (t ≫ j) rfl rfl hi hj
    (C.baseOverlapComparison C' D).hom
  change (pullback t).map (C.schemeTestComparison C' D i j w) ≫ _ =
    _ ≫ C.normalizedOverlapMap C' D _ _ _ hi hj at hn
  rw [C.normalizedOverlapMap_eq_schemeTestComparison C' D _ _ _ hi hj
    (by simpa only [Category.assoc] using congrArg (t ≫ ·) w)] at hn
  simpa only [SheafPullbackPathComparison.comparison, pullbackCongr,
    eqToIso_refl, Iso.trans_refl] using hn

end FLT.Mazur.SchemeAffineDescent.Chart
