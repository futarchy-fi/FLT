/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationUniformVanishingOpen
public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# Uniform vanishing on the direct two-endpoint original relation

Transport the constructed uniform relation neighborhood to the direct
pullback used for original scalar localization. The map preserves the
original arrow and both independently chosen endpoints. Every complete
first-endpoint fiber is retained, with nilpotents and all branches intact.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
local notation "k" => U.ι ≫ first p q I o
local notation "T" => SchemeRelationRestriction.doubleDomain p q k
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
local notation "a" => SchemeRelationRestriction.arrow p q k
local notation "C" => invariantCoordinates (restrictedAction (action e I o) U hU)

omit [Etale p] in
/-- A direct original arrow lifts to the full relation between restricted normalized frames. -/
def doubleToSourceRestriction : T ⟶ SourceRestriction.relation U.ι U.ι :=
  SourceRestriction.lift U.ι U.ι F H a
    (by rw [SchemeRelationRestriction.arrow_fst])
    (by rw [SchemeRelationRestriction.arrow_snd])

omit [Etale p] in
/-- Transport keeps the original first endpoint. -/
@[reassoc] theorem doubleToSourceRestriction_fst :
    doubleToSourceRestriction I o U ≫ SourceRestriction.fst U.ι U.ι = F :=
  SourceRestriction.lift_fst _ _ _ _ _ _ _

omit [Etale p] in
/-- Transport keeps the independent second endpoint. -/
@[reassoc] theorem doubleToSourceRestriction_snd :
    doubleToSourceRestriction I o U ≫ SourceRestriction.snd U.ι U.ι = H :=
  SourceRestriction.lift_snd _ _ _ _ _ _ _

omit [Etale p] in
/-- Transport keeps the unchanged original relation arrow. -/
@[reassoc] theorem doubleToSourceRestriction_arrow :
    doubleToSourceRestriction I o U ≫ SourceRestriction.arrow U.ι U.ι = a :=
  SourceRestriction.lift_arrow _ _ _ _ _ _ _

/-- The actual coefficient-independent open in the direct full relation. -/
def completeDoubleRelationVanishingOpen : (T).Opens :=
  doubleToSourceRestriction I o U ⁻¹ᵁ completeUniformRelationVanishingOpen e I o U hU

omit [Etale p] in
/-- Every invariant coefficient equalizes on the direct relation open. -/
theorem completeDoubleRelationVanishingOpen_equalizes (t : C) :
    ((completeDoubleRelationVanishingOpen e I o U hU).ι ≫ F).appTop t.val =
      ((completeDoubleRelationVanishingOpen e I o U hU).ι ≫ H).appTop t.val := by
  let V := completeUniformRelationVanishingOpen e I o U hU
  have h := congrArg (fun x ↦ ((doubleToSourceRestriction I o U) ∣_ V).appTop x)
    (completeUniformRelationVanishingOpen_equalizes e I o U hU t)
  change (((doubleToSourceRestriction I o U) ∣_ V) ≫ V.ι ≫
    SourceRestriction.fst U.ι U.ι).appTop t.val =
    (((doubleToSourceRestriction I o U) ∣_ V) ≫ V.ι ≫
      SourceRestriction.snd U.ι U.ι).appTop t.val at h
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc,
    doubleToSourceRestriction_fst, ← Category.assoc, morphismRestrict_ι,
    Category.assoc, doubleToSourceRestriction_snd] at h
  exact h

/-- All arrows with complete first endpoint lie in the same direct relation open. -/
theorem completeDoubleRelationVanishingOpen_contains [IsLocallyNoetherian A] :
    (F ≫ U.ι) ⁻¹' completePointLocus (p := p) (q := q) I o ⊆
      completeDoubleRelationVanishingOpen e I o U hU := by
  intro x hx
  apply completeUniformRelationVanishingOpen_contains e I o U hU
  have he := congrArg (fun b ↦ b x)
    (doubleToSourceRestriction_fst_assoc I o U U.ι)
  change (doubleToSourceRestriction I o U ≫ SourceRestriction.fst U.ι U.ι ≫ U.ι) x ∈
      completePointLocus (p := p) (q := q) I o
  rw [he]
  exact hx

end FLT.Mazur.EquivalenceRelationNormalizedFrames
