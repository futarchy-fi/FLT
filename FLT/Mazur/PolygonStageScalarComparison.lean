/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonDegreeZeroScalarExactness
public import FLT.Mazur.SquareZeroScalarGeneration

/-!
# Global functions of every actual infinitesimal polygon stage

The original marking makes structural coefficients injective. Closed
constants start an induction across the square-zero adjacent kernels,
proving that all stage global functions are exactly those coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- The retained marking detects every structural coefficient. -/
theorem stageScalars_injective (m : ℕ) : Function.Injective (stageScalars K m n h) := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Ring K m))).inv).1
  have he := congrArg (marking K m n h ⟨0, by omega⟩).appTop hab
  change ((family K m n h).hom.appTop ≫ (marking K m n h ⟨0, by omega⟩).appTop)
    ((Scheme.ΓSpecIso (.of (Ring K m))).inv a) =
    ((family K m n h).hom.appTop ≫ (marking K m n h ⟨0, by omega⟩).appTop)
      ((Scheme.ΓSpecIso (.of (Ring K m))).inv b) at he
  rw [← Scheme.Hom.comp_appTop, marking_base, Scheme.Hom.id_appTop] at he
  exact he

/-- Structural scalars retain the specified adjacent coefficient restriction. -/
theorem stageRestriction_stageScalars (m : ℕ) (r : Ring K (m + 1)) :
    (stageRestriction K m n h).appTop (stageScalars K (m + 1) n h r) =
      stageScalars K m n h (restriction K m r) := by
  change ((family K (m + 1) n h).hom.appTop ≫ (stageRestriction K m n h).appTop)
    ((Scheme.ΓSpecIso (.of (Ring K (m + 1)))).inv r) = _
  rw [← Scheme.Hom.comp_appTop, stageRestriction_base, Scheme.Hom.comp_appTop]
  change (family K m n h).hom.appTop
    ((baseRestriction K m).appTop ((Scheme.ΓSpecIso (.of (Ring K (m + 1)))).inv r)) = _
  apply congrArg (family K m n h).hom.appTop
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (restriction K m).toRingHom)) r).symm

/-- The original closed fiber inclusion at stage zero is an isomorphism. -/
theorem specialFiberInclusion_zero_isIso : IsIso (specialFiberInclusion K 0 n h) := by
  have hr : Function.Bijective (reduction K 0) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr ?_, reduction_surjective K 0⟩
    intro r hr
    simpa only [Nat.zero_add, pow_one] using reduction_kernel_pow K 0 r hr
  let _ : IsIso (CommRingCat.ofHom (reduction K 0).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hr
  let _ : IsIso (reductionBase K 0) := inferInstanceAs
    (IsIso (Spec.map (CommRingCat.ofHom (reduction K 0).toRingHom)))
  exact (specialFiberInclusion_isPullback K 0 n h).isIso_fst_of_isIso

variable [NeZero n]

/-- Every actual stage-zero global function is an original coefficient. -/
theorem stageScalars_zero_surjective : Function.Surjective (stageScalars K 0 n h) := by
  let _ := specialFiberInclusion_zero_isIso K n h
  intro s
  obtain ⟨r, hr⟩ := (closedPolygon_constantSections K n h).2
    ((specialFiberInclusion K 0 n h).appTop s)
  refine ⟨algebraMap K (Ring K 0) r, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (specialFiberInclusion K 0 n h).appTop).1
  rw [specialFiber_stageScalars, (reduction K 0).commutes]
  exact hr

/-- The actual truncated coefficient map is surjective at every infinitesimal stage. -/
theorem stageScalars_surjective (m : ℕ) : Function.Surjective (stageScalars K m n h) := by
  induction m with
  | zero => exact stageScalars_zero_surjective K n h
  | succ m ih =>
    apply SquareZeroScalarGeneration.surjective (stageScalars K (m + 1) n h)
      (stageRestriction K m n h).appTop.hom (parameter K (m + 1) ^ (m + 1))
    · intro s
      obtain ⟨r, hr⟩ := ih s
      obtain ⟨t, ht⟩ := restriction_surjective K m r
      refine ⟨t, ?_⟩
      change (stageRestriction K m n h).appTop (stageScalars K (m + 1) n h t) = s
      rw [stageRestriction_stageScalars, ht, hr]
    · intro s
      rw [map_pow]
      exact stageRestriction_appTop_kernel K n h m s
    · rw [← map_mul, ← pow_add, pow_eq_zero_of_le (by omega) (parameter_pow K (m + 1)),
        map_zero]

/-- The coefficient comparison is bijective with its original structural map retained. -/
theorem stageScalars_bijective (m : ℕ) : Function.Bijective (stageScalars K m n h) :=
  ⟨stageScalars_injective K n h m, stageScalars_surjective K n h m⟩

end FLT.Mazur.PolygonInfinitesimalStages
