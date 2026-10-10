/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialDiagramRefinement
public import FLT.Mazur.FiniteTypeDiagramStages

/-!
# Cofinal finite-type diagram refinement with original recovery

Advance all source and target relation sets simultaneously while preserving
every old arrow and its full recovery square with the original algebra map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {E : Type w} [Finite E]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)] (src dst : E → ι)

/-- All old finite-type diagram arrows have cofinal simultaneous refinements. -/
theorem exists_finiteType_diagram_refinement
    (f : ∀ e, A (src e) →ₐ[R] A (dst e))
    (s b : ∀ i, Finset (relationIdeal R (A i)))
    (g : ∀ e, Stage R (A (src e)) (s (src e)) →ₐ[R]
      Stage R (A (dst e)) (s (dst e)))
    (hg : ∀ e, (stageMap R (A (dst e)) (s (dst e))).comp (g e) =
      (f e).comp (stageMap R (A (src e)) (s (src e)))) :
    ∃ (t : ∀ i, Finset (relationIdeal R (A i))) (hst : s ≤ t), b ≤ t ∧
      ∃ k : ∀ e, Stage R (A (src e)) (t (src e)) →ₐ[R]
        Stage R (A (dst e)) (t (dst e)),
        (∀ e, (k e).comp (FiniteRelationModel.transition R
          (relationIdeal R (A (src e))) (hst (src e))) =
            (FiniteRelationModel.transition R
              (relationIdeal R (A (dst e))) (hst (dst e))).comp (g e)) ∧
        ∀ e, (stageMap R (A (dst e)) (t (dst e))).comp (k e) =
          (f e).comp (stageMap R (A (src e)) (t (src e))) := by
  let f' (e) := (quotientEquiv R (A (dst e))).symm.toAlgHom.comp
    ((f e).comp (quotientEquiv R (A (src e))).toAlgHom)
  have hfac (e) : (FiniteRelationModel.toQuotient R
      (relationIdeal R (A (dst e))) (s (dst e))).comp (g e) =
        (f' e).comp (FiniteRelationModel.toQuotient R
          (relationIdeal R (A (src e))) (s (src e))) := by
    apply AlgHom.ext
    intro z
    apply (quotientEquiv R (A (dst e))).injective
    change stageMap R (A (dst e)) (s (dst e)) (g e z) =
      quotientEquiv R (A (dst e)) ((quotientEquiv R (A (dst e))).symm
        (f e (stageMap R (A (src e)) (s (src e)) z)))
    rw [AlgEquiv.apply_symm_apply]
    exact AlgHom.congr_fun (hg e) z
  obtain ⟨t, hst, hbt, k, hk, _⟩ := FinitePolynomialCoefficients.exists_diagram_refinement
    (fun i ↦ numGenerators R (A i)) src dst (fun i ↦ relationIdeal R (A i))
    s b g f' hfac
  refine ⟨t, hst, hbt, k, hk, fun e ↦ ?_⟩
  apply (AlgHom.cancel_right (FiniteRelationModel.transition_surjective R
    (relationIdeal R (A (src e))) (hst (src e)))).mp
  rw [AlgHom.comp_assoc, hk, ← AlgHom.comp_assoc, stageMap_transition, hg,
    AlgHom.comp_assoc, stageMap_transition]

end FLT.Mazur.FiniteTypeRelationModel
