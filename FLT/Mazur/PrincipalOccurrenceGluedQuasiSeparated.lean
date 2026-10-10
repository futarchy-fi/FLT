/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluedFiniteness
public import FLT.Mazur.GlueDataQuasiSeparated
public import FLT.Mazur.OpenImageUnionCompact

/-!
# Quasi-separatedness of the actual finite stages

Each common occurrence union has a finite cover by literal affine overlaps.
These compact gluing overlaps prove quasi-separatedness of every stage and
of its structure map to the original affine base.
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


variable [Finite κ] [∀ i, Finite (J i)]

/-- Every common occurrence union is compact. -/
instance principalOccurrenceCommonUnion_compactSpace
    (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
    (hx : ∀ i k, Function.Bijective (x.hom i k)) (i t : ι) :
    CompactSpace (principalOccurrenceCommonUnion e x hx i t).toScheme := by
  let _ (p : PrincipalOccurrenceCommon dst i t) :
      CompactSpace (Spec (.of (PrincipalStage R (B p.1) (b p.1) (x.target p.1)))) :=
    inferInstance
  exact openImageUnion_compactSpace (principalOccurrenceCommonLeft e x hx i t)

variable [Small.{u} ι]

/-- The glued-stage overlaps are the compact common unions. -/
instance principalOccurrenceStageGlueData_overlap_compactSpace
    (x : PrincipalOccurrenceGluingStage e) (p : Shrink.{u} ι × Shrink.{u} ι) :
    CompactSpace ((principalOccurrenceStageGlueData e x).V p) :=
  principalOccurrenceCommonUnion_compactSpace e x.val (principalOccurrenceGluingBijective e x)
    ((equivShrink.{u} ι).symm p.1) ((equivShrink.{u} ι).symm p.2)

/-- Every actual finite stage is quasi-separated. -/
instance principalOccurrenceStageGlueData_quasiSeparatedSpace
    (x : PrincipalOccurrenceGluingStage e) :
    QuasiSeparatedSpace (principalOccurrenceStageGlueData e x).glued := by
  let _ (i : (principalOccurrenceStageGlueData e x).J) :
      IsAffine ((principalOccurrenceStageGlueData e x).U i) :=
    inferInstanceAs (IsAffine (Spec (.of (Stage R (A ((equivShrink.{u} ι).symm i))
      (x.val.source ((equivShrink.{u} ι).symm i))))))
  let _ (p : (principalOccurrenceStageGlueData e x).J ×
      (principalOccurrenceStageGlueData e x).J) :
      CompactSpace ((principalOccurrenceStageGlueData e x).V p) :=
    principalOccurrenceStageGlueData_overlap_compactSpace e x p
  exact glueData_quasiSeparatedSpace (principalOccurrenceStageGlueData e x)

/-- The actual map to the original base is quasi-separated. -/
instance principalOccurrenceGluedStructure_quasiSeparated
    (x : PrincipalOccurrenceGluingStage e) :
    QuasiSeparated (principalOccurrenceGluedStructure e x) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
