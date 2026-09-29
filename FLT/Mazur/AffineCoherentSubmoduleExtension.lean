/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Compatible submodules on a finite family of principal opens

This is the coefficient-module part of affine coherent submodule extension.
Contract the submodules from the principal localizations and intersect the
contractions. Compatibility on pairwise products makes localization of this
intersection recover each prescribed submodule. For a finite module over a
Noetherian ring the intersection is finite.

The passage from a coherent subsheaf on an open subscheme to these coefficient
data, and equality of the resulting sheaf subobjects, are separate steps.
-/

@[expose] public noncomputable section

open Submodule

universe u v

namespace FLT.Mazur.AffineCoherentSubmoduleExtension

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Membership of a global numerator in a localized submodule clears a denominator. -/
lemma numerator_mem_localized_iff (P : Submodule R M) (S : Submonoid R) (m : M) :
    LocalizedModule.mkLinearMap S M m ∈ P.localized S ↔ ∃ s : S, (s : R) • m ∈ P := by
  constructor
  · rintro ⟨x, hx, s, hs⟩
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hs
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists S
      (LocalizedModule.mkLinearMap S M)).mp hs
    refine ⟨t * s, ?_⟩
    rw [Submonoid.coe_mul, mul_smul]
    change (t : R) • x = (t : R) • (s : R) • m at ht
    rw [← ht]
    exact P.smul_mem (t : R) hx
  · rintro ⟨s, hs⟩
    exact ⟨(s : R) • m, hs, s, IsLocalizedModule.mk'_cancel _ m s⟩

/-- On a principal open the denominator can be taken to be a power. -/
lemma numerator_mem_away_iff (P : Submodule R M) (f : R) (m : M) :
    LocalizedModule.mkLinearMap (.powers f) M m ∈ P.localized (.powers f) ↔
      ∃ n : ℕ, f ^ n • m ∈ P := by
  rw [numerator_mem_localized_iff]
  constructor
  · rintro ⟨⟨_, n, rfl⟩, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨_, n, rfl⟩, hn⟩

/-- Contraction of a submodule from a principal localization. -/
def principalContraction (f : R)
    (N : Submodule (Localization.Away f) (LocalizedModule (.powers f) M)) : Submodule R M :=
  (N.restrictScalars R).comap (LocalizedModule.mkLinearMap (.powers f) M)

/-- Localizing a contraction recovers the prescribed submodule as an equality. -/
lemma principalContraction_localized (f : R)
    (N : Submodule (Localization.Away f) (LocalizedModule (.powers f) M)) :
    (principalContraction f N).localized (.powers f) = N :=
  (Submodule.localized'gi (Localization.Away f) (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) M)).l_u_eq N

/-- A contracted submodule is saturated with respect to its principal denominator. -/
lemma principalContraction_pow_mem_iff (f : R)
    (N : Submodule (Localization.Away f) (LocalizedModule (.powers f) M))
    (n : ℕ) (m : M) : f ^ n • m ∈ principalContraction f N ↔
      m ∈ principalContraction f N := by
  change LocalizedModule.mkLinearMap (.powers f) M (f ^ n • m) ∈ N ↔ _
  rw [map_smul, ← algebraMap_smul (Localization.Away f)]
  exact N.smul_mem_iff_of_isUnit
    (IsLocalization.map_units (Localization.Away f) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f))

/-- Localization commutes with a finite intersection of coefficient submodules. -/
lemma localized_iInf_finite {ι : Type*} [Finite ι] (P : ι → Submodule R M)
    (S : Submonoid R) :
    (⨅ i, P i).localized S = ⨅ i, (P i).localized S := by
  let indexFintype : Fintype ι := Fintype.ofFinite ι
  simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Function.comp_apply,
    Submodule.IsLocalizedModule.localized'FrameHom_apply] using
    map_finset_inf (Submodule.localized'FrameHom (Localization S) S
      (LocalizedModule.mkLinearMap S M)) Finset.univ P

variable {ι : Type*} (f : ι → R)
  (N : ∀ i, Submodule (Localization.Away (f i)) (LocalizedModule (.powers (f i)) M))

/-- Global numerators satisfying every prescribed principal-open condition. -/
def compatibleExtension : Submodule R M := ⨅ i, principalContraction (f i) (N i)

/-- The overlap condition is equality inside the ambient module localized at each product. -/
def Compatible : Prop := ∀ i j,
  (principalContraction (f i) (N i)).localized (.powers (f i * f j)) =
    (principalContraction (f j) (N j)).localized (.powers (f i * f j))

/-- Overlap compatibility clears a power of the source denominator in any other chart. -/
lemma compatible_clear_denominator (h : Compatible f N) (i j : ι) (m : M)
    (hm : m ∈ principalContraction (f i) (N i)) :
    ∃ n : ℕ, f i ^ n • m ∈ principalContraction (f j) (N j) := by
  have hi : LocalizedModule.mkLinearMap (.powers (f i * f j)) M m ∈
      (principalContraction (f i) (N i)).localized (.powers (f i * f j)) :=
    (numerator_mem_away_iff _ _ _).mpr ⟨0, by simpa using hm⟩
  rw [h i j] at hi
  obtain ⟨n, hn⟩ := (numerator_mem_away_iff _ _ _).mp hi
  refine ⟨n, (principalContraction_pow_mem_iff (f j) (N j) n _).mp ?_⟩
  simpa only [mul_pow, mul_smul, smul_comm (f i ^ n) (f j ^ n)] using hn

/-- The prescribed submodule lies in the localization of every compatible contraction. -/
lemma le_localized_principalContraction (h : Compatible f N) (i j : ι) :
    N i ≤ (principalContraction (f j) (N j)).localized (.powers (f i)) := by
  rw [← principalContraction_localized (f i) (N i)]
  apply (Submodule.localized'gi (Localization.Away (f i)) (.powers (f i))
    (LocalizedModule.mkLinearMap (.powers (f i)) M)).gc _ _ |>.mpr
  intro m hm
  exact (numerator_mem_away_iff _ _ _).mpr (compatible_clear_denominator f N h i j m hm)

/-- The constructed intersection recovers each prescribed localized submodule exactly. -/
theorem compatibleExtension_localized [Finite ι] (h : Compatible f N) (i : ι) :
    (compatibleExtension f N).localized (.powers (f i)) = N i := by
  rw [compatibleExtension, localized_iInf_finite]
  apply le_antisymm
  · exact (iInf_le _ i).trans_eq (principalContraction_localized (f i) (N i))
  · exact le_iInf (le_localized_principalContraction f N h i)

/-- Every local section lifts to the common extension after multiplying by a power. -/
theorem compatibleExtension_clear_section [Finite ι] (h : Compatible f N) (i : ι)
    (x : LocalizedModule (.powers (f i)) M) (hx : x ∈ N i) :
    ∃ (n : ℕ) (m : M), m ∈ compatibleExtension f N ∧
      f i ^ n • x = LocalizedModule.mkLinearMap (.powers (f i)) M m := by
  rw [← compatibleExtension_localized f N h i] at hx
  obtain ⟨m, hm, ⟨_, n, rfl⟩, he⟩ := hx
  exact ⟨n, m, hm, (IsLocalizedModule.mk'_eq_iff.mp he).symm⟩

/-- Every simultaneous extension is contained in the constructed extension. -/
theorem le_compatibleExtension_iff (P : Submodule R M) :
    P ≤ compatibleExtension f N ↔ ∀ i, P.localized (.powers (f i)) ≤ N i := by
  simp only [compatibleExtension, le_iInf_iff]
  exact forall_congr' fun i ↦ (Submodule.localized'gi (Localization.Away (f i))
    (.powers (f i)) (LocalizedModule.mkLinearMap (.powers (f i)) M)).gc _ _ |>.symm

/-- Compatible principal data in a finite Noetherian module have a finite common extension. -/
theorem exists_finite_compatibleExtension [IsNoetherianRing R] [Module.Finite R M]
    [Finite ι] (h : Compatible f N) :
    ∃ P : Submodule R M, Module.Finite R P ∧
      ∀ i, P.localized (.powers (f i)) = N i :=
  ⟨compatibleExtension f N, inferInstance, compatibleExtension_localized f N h⟩

end FLT.Mazur.AffineCoherentSubmoduleExtension
