/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologyCoordinates
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Deleting an index from supported tuple cochains

Restriction to tuples avoiding an index gives a short exact sequence. Its
surjectivity is proved by extension by zero. Tuples may have repeated entries
and the complexes are unbounded in positive degrees.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

open TwistGradedCech

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Cochains vanishing on tuples that fail to contain the required set. -/
def supportTerm (S : Set ι) (q : ℕ) : Submodule R ((Fin (q + 1) → ι) → R) where
  carrier := {x | ∀ a, ¬ S ⊆ Set.range a → x a = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro a ha
    simp only [Pi.add_apply, hx a ha, hy a ha, add_zero]
  smul_mem' r x hx := by
    intro a ha
    simp only [Pi.smul_apply, hx a ha, smul_zero]

/-- The alternating tuple differential on set-supported cochains. -/
def supportDifferential (S : Set ι) (q : ℕ) :
    supportTerm R ι S q →ₗ[R] supportTerm R ι S (q + 1) where
  toFun x := ⟨fun a ↦ ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • x.val (a ∘ k.succAbove),
    by
      intro a ha
      apply Finset.sum_eq_zero
      intro k _
      rw [x.property _ (fun h ↦ ha (h.trans (Set.range_comp_subset_range _ _))), smul_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    funext a
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    apply Subtype.ext
    funext a
    change (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
      (r • x.val (a ∘ k.succAbove))) =
        r • ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • x.val (a ∘ k.succAbove)
    simp only [Finset.smul_sum, smul_comm r]

/-- Forgetting the support embeds into the zero-exponent scalar cochains. -/
def supportForget (S : Set ι) (q : ℕ) (x : supportTerm R ι S q) :
    scalarTerm R ι 0 0 q :=
  ⟨x.val, fun a ha ↦ False.elim (ha ⟨by simp, fun _ _ ↦ by simp⟩)⟩

lemma supportDifferential_sq (S : Set ι) (q : ℕ) (x : supportTerm R ι S q) :
    supportDifferential R ι S (q + 1) (supportDifferential R ι S q x) = 0 := by
  let y := (scalarEquiv R ι 0 0 q).symm (supportForget R ι S q x)
  have h : exponentDifferential R ι 0 (q + 1) 0
      (exponentDifferential R ι 0 q 0 y) = 0 :=
    Subtype.ext (monomialDifferential_sq R ι 0 q y.val)
  have hs := congrArg (scalarEquiv R ι 0 0 (q + 2)) h
  rw [scalarEquiv_d, scalarEquiv_d, LinearEquiv.apply_symm_apply, map_zero] at hs
  apply Subtype.ext
  exact congrArg (fun z : scalarTerm R ι 0 0 (q + 2) ↦ z.val) hs

/-- The unbounded supported tuple complex. -/
def supportComplex (S : Set ι) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (supportTerm R ι S q))
    (fun q ↦ ModuleCat.ofHom (supportDifferential R ι S q)) (fun q ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact supportDifferential_sq R ι S q)

/-- Scalar support is exactly containment of the negative-index set. -/
lemma supported_iff_negative_subset (n : ℤ) (e : ι →₀ ℤ) (he : e.degree = n)
    {m : ℕ} (a : Fin m → ι) :
    Supported ι n e a ↔ {i | e i < 0} ⊆ Set.range a := by
  constructor
  · intro h i hi
    by_contra ha
    exact (not_le_of_gt hi) (h.2 i ha)
  · intro h
    refine ⟨he, fun i hi ↦ ?_⟩
    by_contra hn
    exact hi (h (lt_of_not_ge hn))

/-- Reinterpret the existing scalar coordinates as set-supported cochains. -/
def scalarSupportEquiv (n : ℤ) (e : ι →₀ ℤ) (he : e.degree = n) (q : ℕ) :
    scalarTerm R ι n e q ≃ₗ[R] supportTerm R ι {i | e i < 0} q where
  toFun x := ⟨x.val, fun a ha ↦ x.property a (by
    simpa only [supported_iff_negative_subset ι n e he] using ha)⟩
  invFun x := ⟨x.val, fun a ha ↦ x.property a (by
    simpa only [supported_iff_negative_subset ι n e he] using ha)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual exponent complex is the complex supported on its negative indices. -/
def exponentSupportIso (n : ℤ) (e : ι →₀ ℤ) (he : e.degree = n) :
    exponentComplex R ι n e ≅ supportComplex R ι {i | e i < 0} :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦
    ((scalarEquiv R ι n e q).trans (scalarSupportEquiv R ι n e he q)).toModuleIso)
    (fun p q h ↦ by
      obtain rfl : p + 1 = q := h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [exponentComplex, supportComplex, CochainComplex.of_d]
      apply Subtype.ext
      exact (congrArg Subtype.val (scalarEquiv_d R ι n e p x)).symm)

/-- Weakening the required support includes the corresponding cochain modules. -/
def supportInclusion (S T : Set ι) (h : T ⊆ S) (q : ℕ) :
    supportTerm R ι S q →ₗ[R] supportTerm R ι T q where
  toFun x := ⟨x.val, fun a ha ↦ x.property a (fun hs ↦ ha (h.trans hs))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inclusion commutes with the alternating differential. -/
def supportInclusionHom (S T : Set ι) (h : T ⊆ S) :
    supportComplex R ι S ⟶ supportComplex R ι T :=
  CochainComplex.ofHom (fun q ↦ ModuleCat.ofHom (supportInclusion R ι S T h q))
    (fun _ ↦ by
      simp only [supportComplex, CochainComplex.of_d]
      rfl)

/-- The indices remaining after deletion. -/
abbrev DeletedIndex (j : ι) := {i : ι // i ≠ j}

/-- Restrict to tuples avoiding the deleted index. -/
def deletionRestriction (S : Set ι) (j : ι) (q : ℕ) :
    supportTerm R ι (S \ {j}) q →ₗ[R]
      supportTerm R (DeletedIndex ι j) (Subtype.val ⁻¹' S) q where
  toFun x := ⟨fun a ↦ x.val (Subtype.val ∘ a), by
    intro a ha
    apply x.property
    intro h
    apply ha
    intro i hi
    obtain ⟨k, hk⟩ := h ⟨hi, i.property⟩
    exact ⟨k, Subtype.ext hk⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction is a map of the unbounded tuple complexes. -/
def deletionRestrictionHom (S : Set ι) (j : ι) :
    supportComplex R ι (S \ {j}) ⟶
      supportComplex R (DeletedIndex ι j) (Subtype.val ⁻¹' S) :=
  CochainComplex.ofHom (fun q ↦ ModuleCat.ofHom (deletionRestriction R ι S j q))
    (fun _ ↦ by
      simp only [supportComplex, CochainComplex.of_d]
      rfl)

/-- Extend a cochain by zero on every tuple containing the deleted index. -/
def deletionExtension (S : Set ι) (j : ι) (q : ℕ) :
    supportTerm R (DeletedIndex ι j) (Subtype.val ⁻¹' S) q →ₗ[R]
      supportTerm R ι (S \ {j}) q := by
  classical
  refine
    { toFun := fun x ↦ ⟨fun a ↦ if h : ∀ k, a k ≠ j then
        x.val (fun k ↦ ⟨a k, h k⟩) else 0, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro a ha
    dsimp only
    split_ifs with h
    · apply x.property
      intro hs
      apply ha
      intro i hi
      obtain ⟨k, hk⟩ := hs (show (⟨i, hi.2⟩ : DeletedIndex ι j) ∈
        Subtype.val ⁻¹' S from hi.1)
      exact ⟨k, congrArg Subtype.val hk⟩
    · rfl
  · intro x y
    apply Subtype.ext
    funext a
    dsimp
    split_ifs <;> simp
  · intro r x
    apply Subtype.ext
    funext a
    dsimp
    split_ifs <;> simp

lemma deletionRestriction_extension (S : Set ι) (j : ι) (q : ℕ)
    (x : supportTerm R (DeletedIndex ι j) (Subtype.val ⁻¹' S) q) :
    deletionRestriction R ι S j q (deletionExtension R ι S j q x) = x := by
  classical
  apply Subtype.ext
  funext a
  change (if h : ∀ k, (a k).val ≠ j then
    x.val (fun k ↦ ⟨(a k).val, h k⟩) else 0) = x.val a
  rw [dite_eq_left (fun k ↦ (a k).property)]

lemma deletionRestriction_surjective (S : Set ι) (j : ι) (q : ℕ) :
    Function.Surjective (deletionRestriction R ι S j q) :=
  fun x ↦ ⟨deletionExtension R ι S j q x, deletionRestriction_extension R ι S j q x⟩

lemma deletionInclusion_injective (S : Set ι) (j : ι) (q : ℕ) :
    Function.Injective (supportInclusion R ι S (S \ {j}) Set.sdiff_subset q) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : supportTerm R ι (S \ {j}) q ↦ z.val) h)

lemma deletion_composite (S : Set ι) (j : ι) (hj : j ∈ S) (q : ℕ)
    (x : supportTerm R ι S q) :
    deletionRestriction R ι S j q
      (supportInclusion R ι S (S \ {j}) Set.sdiff_subset q x) = 0 := by
  apply Subtype.ext
  funext a
  apply x.property
  intro h
  obtain ⟨k, hk⟩ := h hj
  exact (a k).property hk

lemma deletion_exact (S : Set ι) (j : ι) (hj : j ∈ S) (q : ℕ) :
    Function.Exact (supportInclusion R ι S (S \ {j}) Set.sdiff_subset q)
      (deletionRestriction R ι S j q) := by
  intro x
  constructor
  · intro hx
    refine ⟨⟨x.val, ?_⟩, rfl⟩
    intro a ha
    by_cases h : ∀ k, a k ≠ j
    · exact congrArg (fun y ↦ y.val (fun k ↦ ⟨a k, h k⟩)) hx
    · apply x.property
      intro hs
      apply ha
      intro i hi
      by_cases hij : i = j
      · subst i
        simpa only [Set.mem_range, not_forall, not_not] using h
      · exact hs ⟨hi, hij⟩
  · rintro ⟨y, rfl⟩
    exact deletion_composite R ι S j hj q y

/-- The deletion sequence, with its actual inclusion and restriction maps. -/
def deletionSequence (S : Set ι) (j : ι) (hj : j ∈ S) :
    ShortComplex (CochainComplex (ModuleCat R) ℕ) where
  X₁ := supportComplex R ι S
  X₂ := supportComplex R ι (S \ {j})
  X₃ := supportComplex R (DeletedIndex ι j) (Subtype.val ⁻¹' S)
  f := supportInclusionHom R ι S (S \ {j}) Set.sdiff_subset
  g := deletionRestrictionHom R ι S j
  zero := by
    ext q x
    exact deletion_composite R ι S j hj q x

/-- The deletion sequence is short exact, proved degreewise by extension by zero. -/
lemma deletion_shortExact (S : Set ι) (j : ι) (hj : j ∈ S) :
    (deletionSequence R ι S j hj).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    exact fun x hx ↦ (deletion_exact R ι S j hj q x).mp hx
  · exact (ModuleCat.mono_iff_injective _).mpr (deletionInclusion_injective R ι S j q)
  · exact (ModuleCat.epi_iff_surjective _).mpr (deletionRestriction_surjective R ι S j q)

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
