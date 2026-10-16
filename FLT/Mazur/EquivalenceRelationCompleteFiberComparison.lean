/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedScalarComplete

/-!
# The entire original relation fiber over a complete frame

After base change to a complete geometric first endpoint, the open comparison
with the permutation relation is an isomorphism onto the whole original fiber.
This keeps the independent second endpoint, coefficient morphisms and nilpotents.
It does not assert a compatible neighborhood of the frame in the source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {K : Type} [Field K] (u : Spec (.of K) ⟶ source p q I o)

/-- The comparison pulled back to the entire original first-endpoint fiber. -/
def completeRelationFiberComparison :
    pullback (relationComparison e I o) (pullback.fst (relationFirst p q I o) u) ⟶
      pullback (relationFirst p q I o) u := pullback.snd _ _

/-- The comparison is open before any completeness assumption. -/
instance completeRelationFiberComparison_isOpenImmersion :
    IsOpenImmersion (completeRelationFiberComparison e I o u) := by
  let _ := relationComparison_isOpenImmersion e I o
  exact inferInstanceAs (IsOpenImmersion (pullback.snd _ _))

/-- Every field-valued test of the entire fiber has a complete original first endpoint. -/
theorem complete_relationFiber_test (hu : Complete I o u)
    {L : Type} [Field L] (z : Spec (.of L) ⟶ pullback (relationFirst p q I o) u) :
    Complete I o (z ≫ pullback.fst (relationFirst p q I o) u ≫ relationFirst p q I o) := by
  rw [pullback.condition, ← Category.assoc]
  exact complete_scalar I o u (z ≫ pullback.snd _ _) hu

/-- No point of the original relation fiber is omitted by the permutation comparison. -/
theorem completeRelationFiberComparison_surjective (hu : Complete I o u) :
    Function.Surjective (completeRelationFiberComparison e I o u) := by
  intro x
  let z := (pullback (relationFirst p q I o) u).fromSpecResidueField x
  have hc := complete_relationFiber_test I o u hu z
  obtain ⟨w, hw⟩ := complete_first_factors_relationComparison e I o
    (z ≫ pullback.fst (relationFirst p q I o) u) (by
      simpa only [Category.assoc] using hc)
  let v := pullback.lift w z hw
  refine ⟨v default, ?_⟩
  change (v ≫ pullback.snd _ _) default = x
  rw [pullback.lift_snd]
  exact Scheme.fromSpecResidueField_apply x default

/-- The full original fiber comparison is an isomorphism, including scheme structure. -/
theorem completeRelationFiberComparison_isIso (hu : Complete I o u) :
    IsIso (completeRelationFiberComparison e I o u) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, ⟨completeRelationFiberComparison_surjective e I o u hu⟩⟩

/-- Scheme-level identification over the complete geometric first endpoint. -/
def completeRelationFiberIso (hu : Complete I o u) :
    pullback (relationComparison e I o) (pullback.fst (relationFirst p q I o) u) ≅
      pullback (relationFirst p q I o) u := by
  let _ := completeRelationFiberComparison_isIso e I o u hu
  exact asIso (completeRelationFiberComparison e I o u)

/-- The isomorphism retains the original full relation morphism. -/
@[reassoc] theorem completeRelationFiberIso_original (hu : Complete I o u) :
    (completeRelationFiberIso e I o u hu).hom ≫ pullback.fst (relationFirst p q I o) u =
      pullback.fst (relationComparison e I o) (pullback.fst (relationFirst p q I o) u) ≫
        relationComparison e I o := pullback.condition.symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames
