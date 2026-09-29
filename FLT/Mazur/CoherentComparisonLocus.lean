/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentSupport

/-!
# The isomorphism locus of a coherent comparison

A morphism of coherent sheaves on a locally Noetherian scheme is invertible on
the complement of the supports of its kernel and cokernel. This open contains
precisely the points where its stalk map is invertible. In particular a given
comparison which is invertible at a generic point becomes an isomorphism after
shrinking, with both error supports avoiding that point.

These results control an existing sheaf morphism; extending a prescribed stalk
morphism to a sheaf morphism is a separate construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}}

instance comparisonStalk_finiteLimits (x : X) : PreservesFiniteLimits (stalk x) :=
  inferInstanceAs (PreservesFiniteLimits
    (moduleToSheaf X ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)))

instance comparisonStalk_finiteColimits (x : X) : PreservesFiniteColimits (stalk x) :=
  inferInstanceAs (PreservesFiniteColimits
    (moduleToSheaf X ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)))

variable {M N : X.Modules}

/-- The kernel support detects precisely the failure of injectivity on stalks. -/
lemma notMem_support_kernel_iff (f : M ⟶ N) (x : X) :
    x ∉ support (kernel f) ↔ Mono ((stalk x).map f) := by
  change ¬¬ IsZero ((stalk x).obj (kernel f)) ↔ _
  rw [not_not, (PreservesKernel.iso (stalk x) f).isZero_iff]
  exact ⟨fun h ↦ Abelian.mono_of_kernel_ι_eq_zero _ (h.eq_of_src _ _),
    fun _ ↦ isZero_kernel_of_mono _⟩

/-- The cokernel support detects precisely the failure of surjectivity on stalks. -/
lemma notMem_support_cokernel_iff (f : M ⟶ N) (x : X) :
    x ∉ support (cokernel f) ↔ Epi ((stalk x).map f) := by
  change ¬¬ IsZero ((stalk x).obj (cokernel f)) ↔ _
  rw [not_not, (PreservesCokernel.iso (stalk x) f).isZero_iff]
  exact ⟨fun h ↦ Abelian.epi_of_cokernel_π_eq_zero _ (h.eq_of_tgt _ _),
    fun _ ↦ isZero_cokernel_of_epi _⟩

/-- A stalk isomorphism is equivalent to simultaneous vanishing of the two error stalks. -/
lemma isIso_stalk_iff_notMem_support (f : M ⟶ N) (x : X) :
    IsIso ((stalk x).map f) ↔
      x ∉ support (kernel f) ∧ x ∉ support (cokernel f) := by
  rw [notMem_support_kernel_iff, notMem_support_cokernel_iff]
  exact ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ isIso_of_mono_of_epi _⟩

/-- The support of a quotient is contained in the support of its source. -/
lemma support_subset_of_epi (f : M ⟶ N) [Epi f] : support N ⊆ support M := by
  intro x hx hM
  exact hx (hM.of_epi ((stalk x).map f))

/-- A restriction vanishes exactly when its open misses the original support. -/
lemma isZero_restrict_iff (M : X.Modules) (U : X.Opens) :
    IsZero (M.restrict U.ι) ↔ ∀ x ∈ U, x ∉ support M := by
  rw [← support_eq_empty_iff_isZero, support_restrict, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h x hx ↦ h ⟨x, hx⟩, fun h x ↦ h x.val x.property⟩

/-- Error supports inherit the support bound of the source and target. -/
lemma comparison_error_support_subset (f : M ⟶ N) :
    support (kernel f) ∪ support (cokernel f) ⊆ support M ∪ support N :=
  Set.union_subset_union (support_subset_of_mono (kernel.ι f))
    (support_subset_of_epi (cokernel.π f))

section Coherent

variable [IsLocallyNoetherian X] [M.IsFinitePresentation] [N.IsFinitePresentation]

/-- The open complement of the kernel and cokernel supports. -/
def comparisonOpen (f : M ⟶ N) : X.Opens := by
  have := coherent_kernel f
  have := coherent_cokernel f
  exact ⟨(support (kernel f) ∪ support (cokernel f))ᶜ,
    ((isClosed_support (kernel f)).union (isClosed_support (cokernel f))).isOpen_compl⟩

/-- Membership in the comparison open is exactly stalkwise invertibility. -/
lemma mem_comparisonOpen_iff (f : M ⟶ N) (x : X) :
    x ∈ comparisonOpen f ↔ IsIso ((stalk x).map f) := by
  change ¬ (x ∈ support (kernel f) ∨ x ∈ support (cokernel f)) ↔ _
  rw [not_or, ← isIso_stalk_iff_notMem_support]

/-- Stalkwise invertibility is an open condition for a coherent comparison. -/
theorem isOpen_isIso_stalk (f : M ⟶ N) :
    IsOpen {x : X | IsIso ((stalk x).map f)} := by
  convert (comparisonOpen f).isOpen using 1
  ext x
  exact (mem_comparisonOpen_iff f x).symm

/-- Both error sheaves vanish on any open inside the isomorphism locus. -/
lemma comparison_errors_restrict_isZero (f : M ⟶ N) (U : X.Opens)
    (hU : U ≤ comparisonOpen f) :
    IsZero ((kernel f).restrict U.ι) ∧ IsZero ((cokernel f).restrict U.ι) := by
  constructor
  · apply (isZero_restrict_iff _ _).mpr
    intro x hx
    exact ((isIso_stalk_iff_notMem_support f x).mp
      ((mem_comparisonOpen_iff f x).mp (hU hx))).1
  · apply (isZero_restrict_iff _ _).mpr
    intro x hx
    exact ((isIso_stalk_iff_notMem_support f x).mp
      ((mem_comparisonOpen_iff f x).mp (hU hx))).2

/-- On every open contained in the comparison locus the actual restricted map is invertible. -/
theorem isIso_restrict_of_le_comparisonOpen (f : M ⟶ N) (U : X.Opens)
    (hU : U ≤ comparisonOpen f) : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  obtain ⟨hk, hc⟩ := comparison_errors_restrict_isZero f U hU
  have hk' : IsZero (kernel (F.map f)) :=
    (PreservesKernel.iso F f).isZero_iff.mp hk
  have hc' : IsZero (cokernel (F.map f)) :=
    (PreservesCokernel.iso F f).isZero_iff.mp hc
  have : Mono (F.map f) := Abelian.mono_of_kernel_ι_eq_zero _ (hk'.eq_of_src _ _)
  have : Epi (F.map f) := Abelian.epi_of_cokernel_π_eq_zero _ (hc'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Shrinking can respect any previously chosen neighborhood of the point. -/
theorem exists_comparison_neighborhood (f : M ⟶ N) (x : X)
    [IsIso ((stalk x).map f)] (V : X.Opens) (hx : x ∈ V) :
    ∃ U : X.Opens, x ∈ U ∧ U ≤ V ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) ∧
      IsZero ((kernel f).restrict U.ι) ∧ IsZero ((cokernel f).restrict U.ι) := by
  refine ⟨V ⊓ comparisonOpen f, ⟨hx, (mem_comparisonOpen_iff f x).mpr inferInstance⟩,
    inf_le_left, isIso_restrict_of_le_comparisonOpen f _ inf_le_right, ?_⟩
  exact comparison_errors_restrict_isZero f _ inf_le_right

/-- The error support is closed and strictly smaller than any common support bound
containing a point where the comparison is invertible. -/
theorem comparison_error_support_ssubset (f : M ⟶ N) (x : X)
    [IsIso ((stalk x).map f)] (Z : Set X) (hx : x ∈ Z)
    (hM : support M ⊆ Z) (hN : support N ⊆ Z) :
    IsClosed (support (kernel f) ∪ support (cokernel f)) ∧
      support (kernel f) ∪ support (cokernel f) ⊂ Z := by
  have := coherent_kernel f
  have := coherent_cokernel f
  refine ⟨(isClosed_support _).union (isClosed_support _),
    (comparison_error_support_subset f).trans (Set.union_subset hM hN), ?_⟩
  intro h
  have hx' := h hx
  have he := (isIso_stalk_iff_notMem_support f x).mp inferInstance
  exact hx'.elim he.1 he.2

end Coherent

end FLT.Mazur.FCurve.CoherentDevissage
