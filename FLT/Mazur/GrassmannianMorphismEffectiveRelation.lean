/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismDenominators
public import FLT.Mazur.GrassmannianMorphismFiniteCover
public import FLT.Mazur.GrassmannianMorphismRelation

/-!
# Effectiveness of the full recovered Grassmannian relation

The finite-cover intersection equals the intersection over all chart refinements.
Its localization is exactly each recovered original relation. Only a finite
intersection is commuted with localization; every ambient relation is retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)

/-- The finite-cover descent relation uses the actual original chart contractions. -/
def ambientMorphismFiniteRelation : Submodule A (A ⊗[R] M) :=
  ⨅ q : ambientMorphismFiniteCoverIndices f, ambientMorphismContraction f hf q.val

/-- The finite intersection already satisfies every original chart refinement condition. -/
theorem ambientMorphismFiniteRelation_eq :
    ambientMorphismFiniteRelation f hf = ambientMorphismRelation f hf := by
  apply le_antisymm
  · intro x hx
    have hx' : ∀ p : ambientMorphismFiniteCoverIndices f,
        x ∈ ambientMorphismContraction f hf p.val := by
      simpa only [ambientMorphismFiniteRelation, Submodule.mem_iInf] using hx
    apply (mem_ambientMorphismRelation f hf x).mpr
    intro q
    change x ∈ ambientMorphismContraction f hf q
    apply PrincipalSubmodulePatching.mem_of_cover_powers
      (fun p : ambientMorphismFiniteCoverIndices f ↦ p.val.2.val)
      (ambientMorphismFiniteCover_span f)
    intro p
    exact ambientMorphismContraction_clear f hf p.val q x
      (hx' p)
  · exact le_iInf fun q ↦ iInf_le _ q.val

/-- Every recovered local numerator lifts into the localization of each finite contraction. -/
theorem ambientMorphismLocalPoint_le_localized_contraction
    (q p : AmbientMorphismCoverIndex f) :
    (ambientMorphismLocalPoint f hf q).val.toSubmodule ≤
      (ambientMorphismContraction f hf p).localized' (Localization.Away q.2.val)
        (.powers q.2.val)
        (AlgebraTensorModule.rTensor R M
          (Algebra.linearMap A (Localization.Away q.2.val))) := by
  rw [← (Submodule.localized'gi (Localization.Away q.2.val) (.powers q.2.val)
    (AlgebraTensorModule.rTensor R M
      (Algebra.linearMap A (Localization.Away q.2.val)))).l_u_eq
        (ambientMorphismLocalPoint f hf q).val.toSubmodule]
  apply (Submodule.localized'gi (Localization.Away q.2.val) (.powers q.2.val)
    (AlgebraTensorModule.rTensor R M
      (Algebra.linearMap A (Localization.Away q.2.val)))).gc _ _ |>.mpr
  intro x hx
  apply (PrincipalSubmodulePatching.numerator_mem_iff
    (B := Localization.Away q.2.val) (.powers q.2.val) _ _ x).mpr
  obtain ⟨n, hn⟩ := ambientMorphismContraction_clear f hf q p x hx
  exact ⟨⟨_, n, rfl⟩, hn⟩

/-- The constructed full global relation is locally effective on every chart refinement. -/
theorem ambientMorphismRelation_localized_eq (q : AmbientMorphismCoverIndex f) :
    (ambientMorphismRelation f hf).localized' (Localization.Away q.2.val)
      (.powers q.2.val)
      (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away q.2.val))) =
        (ambientMorphismLocalPoint f hf q).val.toSubmodule := by
  apply le_antisymm (ambientMorphismRelation_localized_le f hf q)
  rw [← ambientMorphismFiniteRelation_eq f hf, ambientMorphismFiniteRelation,
    PrincipalSubmodulePatching.localized_iInf]
  exact le_iInf fun p ↦ ambientMorphismLocalPoint_le_localized_contraction f hf q p.val

end FLT.Mazur.GrassmannianChart
