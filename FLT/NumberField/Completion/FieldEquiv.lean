/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.DedekindDomain.Completion.Embedding

/-!
# Completion embeddings with an isomorphic local base field

The tensor decomposition of completions also works when the completed base is
presented by an isomorphic field, such as `ℚ_[p]`. The resulting embedding has
image the compositum of that field and the given global extension.
-/

@[expose] public noncomputable section

namespace NumberField

open IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  {F : Type*} [Field F] [Algebra K F]
  (e : v.adicCompletion K ≃ₐ[K] F)
  {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- Scalar action of a presentation of the completed base field on an extension completion. -/
@[instance_reducible] def completionAlgebraOfEquiv (w : v.Extension (𝓞 L)) :
    Algebra F (w.1.adicCompletion L) :=
  ((algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).comp e.symm.toRingHom).toAlgebra

/-- A finite extension completion remains finite over the isomorphic local base field. -/
theorem completion_finiteDimensional_of_equiv (w : v.Extension (𝓞 L)) :
    letI := completionAlgebraOfEquiv v e w
    FiniteDimensional F (w.1.adicCompletion L) := by
  let := completionAlgebraOfEquiv v e w
  apply Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl (w.1.adicCompletion L))
  apply RingHom.ext
  intro x
  change algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (e.symm (e x)) =
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x
  rw [e.symm_apply_apply]

/-- A global embedding factors through a completion over any isomorphic presentation
of the completed base field, and its image is the expected compositum. -/
theorem exists_adicCompletion_embedding_of_equiv
    {Ω : Type*} [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower K F Ω]
    (j : L →ₐ[K] Ω) :
    ∃ w : v.Extension (𝓞 L),
      letI := completionAlgebraOfEquiv v e w
      ∃ g : w.1.adicCompletion L →ₐ[F] Ω,
        (∀ x : L, g (algebraMap L _ x) = j x) ∧
        g.fieldRange = IntermediateField.adjoin F (Set.range j) := by
  let : Algebra (v.adicCompletion K) Ω := Algebra.compHom Ω e.toRingHom
  let : IsScalarTower K (v.adicCompletion K) Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap K Ω x = algebraMap F Ω (e (algebraMap K _ x))
    rw [e.commutes, IsScalarTower.algebraMap_apply K F Ω]
  obtain ⟨w, g, hg⟩ := exists_adicCompletion_embedding v j
  let := completionAlgebraOfEquiv v e w
  let g' : w.1.adicCompletion L →ₐ[F] Ω := {
    __ := g.toRingHom
    commutes' := fun x ↦ by
      change g (algebraMap (v.adicCompletion K) _ (e.symm x)) = algebraMap F Ω x
      rw [g.commutes]
      change algebraMap F Ω (e (e.symm x)) = algebraMap F Ω x
      rw [e.apply_symm_apply] }
  refine ⟨w, g', hg, le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, rfl⟩
    have hy : g y ∈ IntermediateField.adjoin (v.adicCompletion K) (Set.range j) := by
      rw [← fieldRange_eq_adjoin_of_completion_embedding v j w g hg]
      exact ⟨y, rfl⟩
    change g y ∈ IntermediateField.adjoin F (Set.range j)
    suffices h : ∀ z ∈ IntermediateField.adjoin (v.adicCompletion K) (Set.range j),
        z ∈ IntermediateField.adjoin F (Set.range j) from h (g y) hy
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin F _ hx
    | algebraMap x => exact IntermediateField.algebraMap_mem _ (e x)
    | add x y _ _ hx hy => exact add_mem hx hy
    | inv x _ hx => exact inv_mem hx
    | mul x y _ _ hx hy => exact mul_mem hx hy
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact ⟨algebraMap L _ x, hg x⟩

end NumberField
