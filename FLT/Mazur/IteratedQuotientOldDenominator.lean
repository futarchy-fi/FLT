/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedQuotientProjection
public import FLT.Mazur.FiniteRelationIteratedStages
public import FLT.Mazur.PrincipalQuotientDiagramRefinement

/-!
# Representatives of old coordinate denominators with literal stage transport

Lift an actual old-stage denominator before refining. Its projected value at
every later stage is the literal transition of that old element, including
when the old element was produced by an interchart coordinate arrow.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (b : Finset I) (d : FiniteRelationLocalization.Stage I r b)

/-- An unquotiented representative of an actual old principal-stage denominator. -/
def oldDenominatorRepresentative : Localization.Away r :=
  (PrincipalQuotientProjection.projection_surjective
    (FiniteRelationModel.relations I b) r d).choose

/-- The representative recovers the old denominator exactly, before original recovery. -/
@[simp] theorem projection_oldDenominatorRepresentative :
    PrincipalQuotientProjection.projection (FiniteRelationModel.relations I b) r
      (oldDenominatorRepresentative I r b d) = d :=
  (PrincipalQuotientProjection.projection_surjective
    (FiniteRelationModel.relations I b) r d).choose_spec

/-- At any later stage, the same representative gives the actual old coordinate image. -/
theorem projection_oldDenominatorRepresentative_refinement (t : Set.Ici b) :
    PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t.val) r
      (oldDenominatorRepresentative I r b d) =
      FiniteRelationIterated.denominator R I r b d t := by
  rw [← FinitePolynomialCoefficients.principal_transition_projection (R := R) I r t.property,
    projection_oldDenominatorRepresentative]
  rfl

/-- The actual old-denominator stage localizes at the image of its chosen representative. -/
instance oldDenominatorStage_away (t : Set.Ici b) :
    IsLocalization.Away
      (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t.val) r
        (oldDenominatorRepresentative I r b d))
      (FiniteRelationIterated.Stage R I r b d t) := by
  rw [projection_oldDenominatorRepresentative_refinement R I r b d t]
  infer_instance

/-- Projection lands in the literal old-coordinate iterated stage, without replacing its ideal. -/
def oldDenominatorProjection (t : Set.Ici b) :
    Localization.Away (oldDenominatorRepresentative I r b d) →ₐ[R]
      FiniteRelationIterated.Stage R I r b d t := by
  let _ : IsLocalization.Away
      (PrincipalQuotientProjection.projectionAlgHom R (FiniteRelationModel.relations I t.val) r
        (oldDenominatorRepresentative I r b d))
      (FiniteRelationIterated.Stage R I r b d t) := oldDenominatorStage_away R I r b d t
  exact IsLocalization.Away.mapₐ _ _
    (PrincipalQuotientProjection.projectionAlgHom R (FiniteRelationModel.relations I t.val) r)
    (oldDenominatorRepresentative I r b d)

/-- The literal-target projection retains every first-level numerator formula. -/
@[simp] theorem oldDenominatorProjection_algebraMap (t : Set.Ici b)
    (x : Localization.Away r) :
    oldDenominatorProjection R I r b d t (algebraMap _ _ x) =
      algebraMap _ (FiniteRelationIterated.Stage R I r b d t)
        (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t.val) r x) := by
  simp [oldDenominatorProjection, IsLocalization.Away.mapₐ, IsLocalization.Away.map,
    PrincipalQuotientProjection.projectionAlgHom]

/-- Every element of the actual old-coordinate double-open stage has a representative. -/
theorem oldDenominatorProjection_surjective (t : Set.Ici b) :
    Function.Surjective (oldDenominatorProjection R I r b d t) := by
  let _ : IsLocalization.Away
      (PrincipalQuotientProjection.projectionAlgHom R (FiniteRelationModel.relations I t.val) r
        (oldDenominatorRepresentative I r b d))
      (FiniteRelationIterated.Stage R I r b d t) := oldDenominatorStage_away R I r b d t
  exact IsLocalization.Away.mapₐ_surjective_of_surjective _
    (PrincipalQuotientProjection.projection_surjective (FiniteRelationModel.relations I t.val) r)

/-- The canonical representative target identifies with the literal old-coordinate target. -/
def oldDenominatorEquiv (t : Set.Ici b) :
    Target (FiniteRelationModel.relations I t.val) r (oldDenominatorRepresentative I r b d)
      ≃ₐ[R] FiniteRelationIterated.Stage R I r b d t :=
  (IsLocalization.algEquiv
    (Submonoid.powers (PrincipalQuotientProjection.projection
      (FiniteRelationModel.relations I t.val) r (oldDenominatorRepresentative I r b d)))
    (Target (FiniteRelationModel.relations I t.val) r (oldDenominatorRepresentative I r b d))
    (FiniteRelationIterated.Stage R I r b d t)).restrictScalars R

/-- The target identification fixes every element of the shared first principal stage. -/
@[simp] theorem oldDenominatorEquiv_algebraMap (t : Set.Ici b)
    (x : FiniteRelationLocalization.Stage I r t.val) :
    oldDenominatorEquiv R I r b d t (algebraMap _ _ x) =
      algebraMap _ (FiniteRelationIterated.Stage R I r b d t) x :=
  (IsLocalization.algEquiv
    (Submonoid.powers (PrincipalQuotientProjection.projection
      (FiniteRelationModel.relations I t.val) r (oldDenominatorRepresentative I r b d)))
    (Target (FiniteRelationModel.relations I t.val) r (oldDenominatorRepresentative I r b d))
    (FiniteRelationIterated.Stage R I r b d t)).commutes x

/-- The target identification preserves projection on the entire double localization. -/
theorem oldDenominatorEquiv_comp_projection (t : Set.Ici b) :
    (oldDenominatorEquiv R I r b d t).toAlgHom.comp
      (projectionAlgHom (FiniteRelationModel.relations I t.val) r
        (oldDenominatorRepresentative I r b d) R) = oldDenominatorProjection R I r b d t := by
  apply IsLocalization.algHom_ext (Submonoid.powers (oldDenominatorRepresentative I r b d))
  apply DFunLike.ext
  intro x
  change oldDenominatorEquiv R I r b d t
    (projection (FiniteRelationModel.relations I t.val) r
      (oldDenominatorRepresentative I r b d) (algebraMap _ _ x)) =
    oldDenominatorProjection R I r b d t (algebraMap _ _ x)
  rw [projection_algebraMap, oldDenominatorProjection_algebraMap,
    oldDenominatorEquiv_algebraMap]

/-- The literal old-coordinate target imposes exactly the shared ambient relation ideal. -/
theorem ker_oldDenominatorProjection (t : Set.Ici b) :
    RingHom.ker (oldDenominatorProjection R I r b d t).toRingHom =
      ((FiniteRelationModel.relations I t.val).map
        (algebraMap P (Localization.Away r))).map
        (algebraMap (Localization.Away r)
          (Localization.Away (oldDenominatorRepresentative I r b d))) := by
  have h : (Submonoid.powers (oldDenominatorRepresentative I r b d)).map
      (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t.val) r) =
      Submonoid.powers (FiniteRelationIterated.denominator R I r b d t) := by
    rw [Submonoid.map_powers, projection_oldDenominatorRepresentative_refinement R I r b d t]
  have hk := IsLocalization.ker_map
    (S := Localization.Away (oldDenominatorRepresentative I r b d))
    (FiniteRelationIterated.Stage R I r b d t)
    (PrincipalQuotientProjection.projection (FiniteRelationModel.relations I t.val) r) h
  change RingHom.ker (oldDenominatorProjection R I r b d t).toRingHom =
    (RingHom.ker (PrincipalQuotientProjection.projection
      (FiniteRelationModel.relations I t.val) r)).map _ at hk
  simpa only [PrincipalQuotientProjection.ker_projection] using hk

/-- Refinement commutes with projection on the entire old-coordinate double localization. -/
theorem oldDenominatorProjection_transition {t q : Set.Ici b} (h : t ≤ q) :
    (FiniteRelationIterated.transition R I r b d h).comp
      (oldDenominatorProjection R I r b d t) = oldDenominatorProjection R I r b d q := by
  apply IsLocalization.algHom_ext (Submonoid.powers (oldDenominatorRepresentative I r b d))
  apply DFunLike.ext
  intro x
  change FiniteRelationIterated.transition R I r b d h
    (oldDenominatorProjection R I r b d t (algebraMap _ _ x)) =
      oldDenominatorProjection R I r b d q (algebraMap _ _ x)
  rw [oldDenominatorProjection_algebraMap, oldDenominatorProjection_algebraMap,
    FiniteRelationIterated.transition_algebraMap,
    FinitePolynomialCoefficients.principal_transition_projection]

end FLT.Mazur.IteratedQuotientProjection
