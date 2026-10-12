/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectivePrincipalDescent
public import FLT.Mazur.GrassmannianMorphismQuotientLocalization

/-!
# Finite projectivity and rank of the recovered original quotient

Effectiveness and the actual principal cover descend finite presentation and
projectivity. The quotient rank is then detected after localization at every
coefficient prime, retaining the prescribed rank over arbitrary coefficient rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)

/-- The actual original quotient is finitely presented and projective. -/
theorem ambientMorphismQuotient_finiteProjective :
    Module.FinitePresentation A ((A ⊗[R] M) ⧸ ambientMorphismRelation f hf) ∧
    Module.Projective A ((A ⊗[R] M) ⧸ ambientMorphismRelation f hf) := by
  exact PrincipalSubmodulePatching.finiteProjective_of_principal_cover
    (fun q : AmbientMorphismCoverIndex f ↦ q.2.val) (ambientMorphismCover_span f)
    (fun q ↦ Localization.Away q.2.val)
    (fun q ↦ (Localization.Away q.2.val ⊗[R] M) ⧸
      (ambientMorphismLocalPoint f hf q).val.toSubmodule)
    (ambientMorphismQuotientLocalization f hf) (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance)

/-- Finite presentation descends to the constructed quotient, with its entire original relation. -/
instance ambientMorphismQuotient_finitePresentation :
    Module.FinitePresentation A ((A ⊗[R] M) ⧸ ambientMorphismRelation f hf) :=
  (ambientMorphismQuotient_finiteProjective f hf).1

/-- Projectivity descends to the constructed quotient. -/
instance ambientMorphismQuotient_projective :
    Module.Projective A ((A ⊗[R] M) ⧸ ambientMorphismRelation f hf) :=
  (ambientMorphismQuotient_finiteProjective f hf).2

/-- The rank of the constructed original quotient is the prescribed rank at every prime. -/
theorem ambientMorphismQuotient_rank (p : PrimeSpectrum A) :
    Module.rankAtStalk ((A ⊗[R] M) ⧸ ambientMorphismRelation f hf) p = d := by
  obtain ⟨q, hq⟩ := ambientMorphismCover_exists f p
  have hp : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap A (Localization.Away q.2.val))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away q.2.val) q.2.val]
    exact hq
  obtain ⟨z, rfl⟩ := hp
  rw [← Module.rankAtStalk_isBaseChange
    (IsLocalizedModule.isBaseChange (.powers q.2.val) (Localization.Away q.2.val)
      (ambientMorphismQuotientLocalization f hf q)) z]
  exact (ambientMorphismLocalPoint f hf q).val.rankAtStalk_eq z

end FLT.Mazur.GrassmannianChart
