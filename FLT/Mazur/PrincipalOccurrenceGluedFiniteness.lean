/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluedStructure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.Fintype.Shrink

/-!
# Finiteness of the actual finite-stage structure maps

Local finite presentation descends from the literal affine stage charts.
For a finite atlas the glued scheme is compact, so its map to the original
affine base is also quasi-compact.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Small.{u} ι]

/-- The glued stage is locally finitely presented over the original affine base. -/
instance principalOccurrenceGluedStructure_locallyOfFinitePresentation
    (x : PrincipalOccurrenceGluingStage e) :
    LocallyOfFinitePresentation (principalOccurrenceGluedStructure e x) := by
  let _ : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation.{u})
    (principalOccurrenceStageGlueData e x).openCover
  intro i
  change LocallyOfFinitePresentation
    ((principalOccurrenceStageGlueData e x).ι i ≫ principalOccurrenceGluedStructure e x)
  exact (congrArg (fun g ↦ LocallyOfFinitePresentation g)
    (principalOccurrenceGluedStructure_chart e x i)).mpr
      (FiniteRelationModel.stageStructure_locallyOfFinitePresentation R
        (relationIdeal R (A ((equivShrink.{u} ι).symm i))) _)

variable [Finite ι]

/-- Finitely many affine charts make the glued stage compact. -/
instance principalOccurrenceStageGlueData_compactSpace
    (x : PrincipalOccurrenceGluingStage e) :
    CompactSpace (principalOccurrenceStageGlueData e x).glued := by
  let _ : Finite (principalOccurrenceStageGlueData e x).openCover.I₀ :=
    inferInstanceAs (Finite (Shrink.{u} ι))
  let _ (i : (principalOccurrenceStageGlueData e x).openCover.I₀) :
      CompactSpace ((principalOccurrenceStageGlueData e x).openCover.X i) :=
    inferInstanceAs (CompactSpace (Spec (.of (Stage R (A ((equivShrink.{u} ι).symm i))
      (x.val.source ((equivShrink.{u} ι).symm i))))))
  exact (principalOccurrenceStageGlueData e x).openCover.compactSpace

/-- The finite glued stage is quasi-compact over its actual affine base. -/
instance principalOccurrenceGluedStructure_quasiCompact (x : PrincipalOccurrenceGluingStage e) :
    QuasiCompact (principalOccurrenceGluedStructure e x) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
