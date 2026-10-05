/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedChartComparison
public import FLT.Mazur.SectionGradedChartExtension
public import FLT.Mazur.SectionGradedChartKernel

/-!
# Affine generator charts recover their rings of functions

On a finite affine generator cover, chart extension proves surjectivity of
the actual homogeneous localization comparison. Annihilation by a power
of the denominator proves injectivity. No reducedness hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Scheme.Modules
universe u v
namespace FLT.Mazur.SectionGradedChartIsomorphism
open FCurve ModuleLineBundleTensorPullback SectionCover SectionGradedSum
open SectionGradedChartComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  {ι : Type v} [Finite ι] (d : ℕ) (s : ι → Γ(tensorPower L d, ⊤))
  (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤) (i : ι)

include haff hcover

/-- Every chart function is the image of an actual homogeneous fraction. -/
lemma surjective : Function.Surjective (toFunctions L d (s i) (chart s i) le_rfl) := by
  intro a
  obtain ⟨n, t, ht⟩ := SectionGradedChartExtension.numerator L d s haff hcover i a
  have htmem : of L ⊤ (d * n) t ∈ grade L ⊤ (n • d) := by
    simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using
      (show of L ⊤ (d * n) t ∈ grade L ⊤ (d * n) from ⟨t, rfl⟩)
  refine ⟨Away.mk (grade L ⊤) ⟨s i, rfl⟩ n (of L ⊤ (d * n) t) htmem, ?_⟩
  apply SectionGradedGeneratorLocalization.power_smul_injective L d (s i) (chart s i) le_rfl n
  exact (toFunctions_mk_smul L d (s i) (chart s i) le_rfl n _ htmem).trans ht

/-- Only fractions killed by a denominator power vanish as chart functions. -/
lemma injective : Function.Injective (toFunctions L d (s i) (chart s i) le_rfl) := by
  apply (injective_iff_map_eq_zero (toFunctions L d (s i) (chart s i) le_rfl)).mpr
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grade L ⊤)
    (show of L ⊤ d (s i) ∈ grade L ⊤ d from ⟨s i, rfl⟩) z
  have he := toFunctions_mk_smul L d (s i) (chart s i) le_rfl n a ha
  rw [hz, zero_smul] at he
  have ha' : a ∈ grade L ⊤ (d * n) := by
    simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using ha
  obtain ⟨t, rfl⟩ := ha'
  have ht : (tensorPower L (d * n)).presheaf.map
      (homOfLE le_top : chart s i ⟶ ⊤).op t = 0 := by
    apply (SectionGradedRestriction.of_eq_zero_iff L (chart s i) (d * n) _).mp
    exact (restrict_of L _ _ t).symm.trans he.symm
  obtain ⟨m, hm⟩ := SectionGradedChartKernel.exists_pow_mul_eq_zero L d s haff hcover i n t ht
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk']
  exact (IsLocalization.mk'_eq_zero_iff (S := Localization.Away (of L ⊤ d (s i))) _ _).mpr
    ⟨⟨_, m, rfl⟩, hm⟩

/-- Homogeneous localization is isomorphic to the actual affine chart's ring of functions. -/
def ringEquiv : Away (grade L ⊤) (of L ⊤ d (s i)) ≃+* Γ(X, chart s i) :=
  RingEquiv.ofBijective (toFunctions L d (s i) (chart s i) le_rfl)
    ⟨injective L d s haff hcover i, surjective L d s haff hcover i⟩

end FLT.Mazur.SectionGradedChartIsomorphism
