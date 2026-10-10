/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyRelations
public import FLT.Mazur.FiniteTypePrincipalSurjectiveLifts

/-!
# Simultaneous surjectivity of incoming coordinate maps

If all original maps are surjective, any family of lifts has a commuting
refinement with every map surjective. Only the common target is enlarged.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {a : ∀ i, A i} {b : B}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b}

/-- All surjective original coordinate maps become surjective at one common target. -/
theorem exists_principalFamily_surjective (hf : ∀ i, Function.Surjective (f i))
    (x : PrincipalFamilyStage a b f) :
    ∃ y : PrincipalFamilyStage a b f, x ≤ y ∧ y.source = x.source ∧
      ∀ i, Function.Surjective (y.hom i) := by
  classical
  let _ := Fintype.ofFinite ι
  have hx (i) : Function.Surjective ((principalStageMap R B b x.target).comp (x.hom i)) := by
    rw [x.fac i]
    exact (hf i).comp (principalStageMap_surjective R (A i) (a i) (x.source i))
  choose t ht hs using fun i ↦ exists_principal_surjective_stage b x.target (x.hom i) (hx i)
  let q := x.target ∪ Finset.univ.biUnion t
  have hq : x.target ≤ q := Finset.subset_union_left
  have htq (i) : t i ≤ q := by
    intro z hz
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩)
  refine ⟨principalFamilyTargetExtension x q hq,
    principalFamilyTargetExtension_le x q hq, rfl, fun i ↦ ?_⟩
  change Function.Surjective ((principalTransition b hq).comp (x.hom i))
  have he : (principalTransition b hq).comp (x.hom i) =
      (principalTransition b (htq i)).comp
        ((principalTransition b (ht i)).comp (x.hom i)) := by
    rw [← AlgHom.comp_assoc, principalTransition_comp]
  rw [he]
  exact (FiniteRelationLocalization.transition_surjective R (relationIdeal R B)
    (principalRepresentative R B b) (htq i)).comp (hs i)

end FLT.Mazur.FiniteTypeRelationModel
