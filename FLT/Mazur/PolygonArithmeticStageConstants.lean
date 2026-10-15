/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticZeroExactness
public import FLT.Mazur.SquareZeroScalarGeneration

/-!
# Global functions of every actual infinitesimal polygon stage

The original marking makes structural coefficients injective. Closed
constants start an induction across the square-zero adjacent kernels,
proving that all stage global functions are exactly those coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] family

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- The retained marking detects every structural coefficient. -/
theorem stageScalars_injective (m : ℕ) : Function.Injective (stageScalars A π m n h) := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Quotient A π m))).inv).1
  have he := congrArg (marking A π m n h ⟨0, by omega⟩).appTop hab
  change ((family A π m n h).hom.appTop ≫ (marking A π m n h ⟨0, by omega⟩).appTop)
    ((Scheme.ΓSpecIso (.of (Quotient A π m))).inv a) =
    ((family A π m n h).hom.appTop ≫ (marking A π m n h ⟨0, by omega⟩).appTop)
      ((Scheme.ΓSpecIso (.of (Quotient A π m))).inv b) at he
  rw [← Scheme.Hom.comp_appTop, marking_base, Scheme.Hom.id_appTop] at he
  exact he

/-- Structural scalars retain the specified adjacent coefficient restriction. -/
theorem stageRestriction_stageScalars (m : ℕ) (r : Quotient A π (m + 1)) :
    (stageRestriction A π m n h).appTop (stageScalars A π (m + 1) n h r) =
      stageScalars A π m n h (restriction A π m r) := by
  change ((family A π (m + 1) n h).hom.appTop ≫ (stageRestriction A π m n h).appTop)
    ((Scheme.ΓSpecIso (.of (Quotient A π (m + 1)))).inv r) = _
  rw [← Scheme.Hom.comp_appTop, stageRestriction_base, Scheme.Hom.comp_appTop]
  change (family A π m n h).hom.appTop
    ((baseRestriction A π m).appTop ((Scheme.ΓSpecIso (.of (Quotient A π (m + 1)))).inv r)) = _
  apply congrArg (family A π m n h).hom.appTop
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (restriction A π m).toRingHom)) r).symm

variable [IsLocalRing A] (hgen : IsLocalRing.maximalIdeal A = ideal A π)
local notation "K" => IsLocalRing.ResidueField A

include hgen in
/-- The original residue inclusion at arithmetic stage zero is an isomorphism. -/
theorem residueFiberInclusion_zero_isIso :
    IsIso (residueFiberInclusion A π (parameter_residue_zero A π hgen) 0 n h) := by
  let hπ := parameter_residue_zero A π hgen
  have hr : Function.Bijective (residueMap A π hπ 0) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr ?_, residueMap_surjective A π hπ 0⟩
    intro r hr
    obtain ⟨s, hs⟩ := (residueMap_eq_zero_iff A π hgen hπ 0 r).mp hr
    have hz : parameter A π 0 = 0 := by
      simpa only [Nat.zero_add, pow_one] using parameter_pow A π 0
    rw [hz, zero_mul] at hs
    exact hs.symm
  let _ : IsIso (CommRingCat.ofHom (residueMap A π hπ 0)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hr
  let _ : IsIso (residueBase A π hπ 0) := inferInstanceAs
    (IsIso (Spec.map (CommRingCat.ofHom (residueMap A π hπ 0))))
  exact (residueFiberInclusion_isPullback A π hπ 0 n h).isIso_fst_of_isIso

variable [NeZero n]

include hgen in
/-- Every actual arithmetic stage-zero global function is an original coefficient. -/
theorem stageScalars_zero_surjective : Function.Surjective (stageScalars A π 0 n h) := by
  let hπ := parameter_residue_zero A π hgen
  let _ := residueFiberInclusion_zero_isIso A π n h hgen
  intro s
  obtain ⟨r, hr⟩ := (PolygonInfinitesimalStages.closedPolygon_constantSections K n h).2
    ((residueFiberInclusion A π hπ 0 n h).appTop s)
  obtain ⟨t, ht⟩ := residueMap_surjective A π hπ 0 r
  refine ⟨t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (residueFiberInclusion A π hπ 0 n h).appTop).1
  rw [residueFiber_stageScalars, ht]
  exact hr

variable [IsNoetherianRing A] [IsDomain A] (hne : π ≠ 0)

include hgen hne in
/-- The actual truncated coefficient map is surjective at every infinitesimal stage. -/
theorem stageScalars_surjective (m : ℕ) : Function.Surjective (stageScalars A π m n h) := by
  induction m with
  | zero => exact stageScalars_zero_surjective A π n h hgen
  | succ m ih =>
    apply SquareZeroScalarGeneration.surjective (stageScalars A π (m + 1) n h)
      (stageRestriction A π m n h).appTop.hom (parameter A π (m + 1) ^ (m + 1))
    · intro s
      obtain ⟨r, hr⟩ := ih s
      obtain ⟨t, ht⟩ := restriction_surjective A π m r
      refine ⟨t, ?_⟩
      change (stageRestriction A π m n h).appTop (stageScalars A π (m + 1) n h t) = s
      rw [stageRestriction_stageScalars, ht, hr]
    · intro s
      rw [map_pow]
      exact stageRestriction_appTop_kernel A π hgen n h hne m s
    · rw [← map_mul, ← pow_add, pow_eq_zero_of_le (by omega) (parameter_pow A π (m + 1)),
        map_zero]

include hgen hne in
/-- The coefficient comparison is bijective with its original structural map retained. -/
theorem stageScalars_bijective (m : ℕ) : Function.Bijective (stageScalars A π m n h) :=
  ⟨stageScalars_injective A π n h m, stageScalars_surjective A π n h hgen hne m⟩

end FLT.Mazur.PolygonArithmeticStages
