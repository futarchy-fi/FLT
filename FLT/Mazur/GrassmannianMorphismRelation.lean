/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismLocalQuotient
public import FLT.Mazur.GrassmannianPrincipalRelationRecovery

/-!
# A global relation recovered from an arbitrary Grassmannian scheme morphism

Intersect the inverse images of all the recovered local quotient relations.
For a morphism classifying an original quotient this returns its entire original
relation. General local effectiveness and finite projectivity still require descent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)

/-- The candidate full global relation, as the intersection of the actual local inverse images. -/
def ambientMorphismRelation : Submodule A (A ⊗[R] M) :=
  ⨅ q : AmbientMorphismCoverIndex f, Submodule.comap
    (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away q.2.val)))
    ((ambientMorphismLocalPoint f hf q).val.toSubmodule.restrictScalars A)

/-- Membership is tested in every full recovered local quotient relation. -/
theorem mem_ambientMorphismRelation (x : A ⊗[R] M) :
    x ∈ ambientMorphismRelation f hf ↔ ∀ q : AmbientMorphismCoverIndex f,
      AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away q.2.val)) x ∈
        (ambientMorphismLocalPoint f hf q).val.toSubmodule := by
  simp only [ambientMorphismRelation, Submodule.mem_iInf, Submodule.mem_comap,
    Submodule.restrictScalars_mem]

/-- Localizing the constructed relation gives a submodule of each recovered local relation. -/
theorem ambientMorphismRelation_localized_le (q : AmbientMorphismCoverIndex f) :
    (ambientMorphismRelation f hf).localized' (Localization.Away q.2.val)
      (.powers q.2.val)
      (AlgebraTensorModule.rTensor R M (Algebra.linearMap A (Localization.Away q.2.val))) ≤
        (ambientMorphismLocalPoint f hf q).val.toSubmodule := by
  apply ((Submodule.localized'gi (Localization.Away q.2.val) (.powers q.2.val)
    (AlgebraTensorModule.rTensor R M
      (Algebra.linearMap A (Localization.Away q.2.val)))).gc _ _).mpr
  exact iInf_le _ q

/-- Recovering from an original classifying morphism returns its entire original relation. -/
theorem ambientMorphismRelation_ofClassifying {ι : Type u} [Fintype ι]
    (b : Module.Basis ι R M) (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d) :
    ambientMorphismRelation (ambientClassifyingMap b N hκ)
      (ambientClassifyingMap_over b N hκ) = N.toSubmodule := by
  unfold ambientMorphismRelation
  simp_rw [ambientMorphismLocalPoint_ofClassifying]
  exact (grassmannian_relation_eq_iInf _
    (ambientMorphismCover_span (ambientClassifyingMap b N hκ)) N).symm

/-- Any effective original quotient realizing all local recoveries classifies the given morphism. -/
theorem ambientClassifyingMap_eq_of_localRecovery {ι : Type u} [Fintype ι]
    (b : Module.Basis ι R M) (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d)
    (hN : ∀ q : AmbientMorphismCoverIndex f,
      Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away q.2.val)) N =
        (ambientMorphismLocalPoint f hf q).val) :
    ambientClassifyingMap b N hκ = f := by
  apply (ambientMorphismPrincipalCover f).hom_ext
  intro q
  change Spec.algebraMap A (Localization.Away q.2.val) ≫ ambientClassifyingMap b N hκ = _
  exact (ambientClassifyingMap_chartTest b N hκ
    (IsScalarTower.toAlgHom R A (Localization.Away q.2.val)) q.1
    (ambientMorphismLocalPoint f hf q) (hN q).symm).trans
      (ambientMorphismLocalPoint_classifies f hf q)

/-- Any effective recovery has exactly the constructed global relation. -/
theorem ambientMorphismRelation_eq_of_localRecovery
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hN : ∀ q : AmbientMorphismCoverIndex f,
      Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away q.2.val)) N =
        (ambientMorphismLocalPoint f hf q).val) :
    ambientMorphismRelation f hf = N.toSubmodule := by
  unfold ambientMorphismRelation
  simp_rw [← hN]
  exact (grassmannian_relation_eq_iInf _ (ambientMorphismCover_span f) N).symm

end FLT.Mazur.GrassmannianChart
