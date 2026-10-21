/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalBoundaryCoefficients
public import FLT.Mazur.ReducedImmersionFactor

/-!
# Actual reduced-test factors through the full rank-core boundary

The core map is an immersion and the boundary square is Cartesian.
Image containment for a reduced original test therefore constructs its unique
factor through the unchanged full boundary ideal, at the prescribed order.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance reducedFactorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance reducedFactorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance reducedFactorOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (k : ℕ)
set_option quotPrecheck false
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J k
local notation "g" => rankStageCoreOriginalBoundaryMap e n a ha J k
local notation "f" => rankStageCoreOriginalMap e n a ha k

/-- The full original core map is a locally closed immersion. -/
instance rankStageCoreOriginalMap_immersion : IsImmersion f := by
  unfold rankStageCoreOriginalMap rankThickeningMap
  infer_instance

/-- The full boundary map is the base change of that same immersion. -/
instance rankStageCoreOriginalBoundaryMap_immersion : IsImmersion g :=
  MorphismProperty.of_isPullback
    (IdealSheafClosedTransitions.isPullback I J f
      (rankStageCoreOriginalMap_ideal e n a ha J k))
    (inferInstanceAs (IsImmersion f))

/-- A reduced original boundary test has a unique full stage factor from core-image containment. -/
theorem rankStage_boundary_factor_of_range {T : Scheme.{0}} [IsReduced T]
    (t : T ⟶ J.subscheme) (ht : Set.range (t ≫ J.subschemeι) ⊆ Set.range f) :
    ∃! u : T ⟶ (I).subscheme, u ≫ g = t := by
  obtain ⟨v, hv, _⟩ := ReducedImmersionFactor.existsUnique_factor f (t ≫ J.subschemeι) ht
  let H := IdealSheafClosedTransitions.isPullback I J f
    (rankStageCoreOriginalMap_ideal e n a ha J k)
  let u := H.lift v t hv
  have hu : u ≫ g = t := H.lift_snd _ _ _
  exact ⟨u, hu, fun z hz ↦ (cancel_mono g).mp (hz.trans hu.symm)⟩

/-- Original endpoints determine equality of full stage factors. -/
theorem rankStage_boundary_factor_ext {T : Scheme.{0}} (u v : T ⟶ (I).subscheme)
    (h : u ≫ g = v ≫ g) : u = v := (cancel_mono g).mp h

end FLT.Mazur.EquivalenceRelationOrderedFrames
