/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationUniformVanishingOpen
public import FLT.Mazur.SchemeOpenEnvelopeInteriorTests
public import FLT.Mazur.SchemeRelationCoverSourceFunctions
public import FLT.Mazur.EquivalenceRelationCompleteInterior

/-!
# Actual source restrictions with uniform full relation compatibility

Removing the closure of the bad relation image gives a constructed source
open. Every moving-invariant coefficient restricts there to a function
compatible with the whole original relation. Completeness alone is not
asserted to put a point in this source open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
local notation "r" => SourceRestriction.fst U.ι U.ι
local notation "s" => SourceRestriction.snd U.ι U.ι
local notation "C" => invariantCoordinates (restrictedAction (action e I o) U hU)
local notation "O" => completeUniformRelationVanishingOpen e I o U hU

/-- A source open constructed from the whole bad relation, independently of a coefficient. -/
def uniformSourceOpen : U.toScheme.Opens := SchemeOpenEnvelope.fullFiberInterior r O

omit [Etale p] in
/-- All original tests with first endpoint in this source open preserve every coefficient. -/
theorem uniformSourceOpen_test {T : Scheme} (u v : T ⟶ U.toScheme) (a : T ⟶ D)
    (ha : a ≫ p = u ≫ U.ι ≫ first p q I o)
    (hb : a ≫ q = v ≫ U.ι ≫ first p q I o)
    (hu : Set.range u ⊆ uniformSourceOpen e I o U hU) (t : C) :
    u.appTop t.val = v.appTop t.val := by
  let l := SourceRestriction.lift U.ι U.ι u v a ha hb
  have hl : Set.range (l ≫ r) ⊆ SchemeOpenEnvelope.fullFiberInterior r O := by
    simpa only [l, SourceRestriction.lift_fst, uniformSourceOpen] using hu
  let g := SchemeOpenEnvelope.fullFiberInteriorTestLift r O l hl
  have hg : g ≫ (O).ι = l := SchemeOpenEnvelope.fullFiberInteriorTestLift_inclusion r O l hl
  have h := completeUniformRelationVanishingOpen_test e I o U hU g t
  simpa only [← Category.assoc, hg, l, SourceRestriction.lift_fst,
    SourceRestriction.lift_snd] using h

local notation "V" => uniformSourceOpen e I o U hU
local notation "j" => (V).ι ≫ U.ι ≫ first p q I o
local notation "rj" => SchemeRelationRestriction.fst p q j
local notation "sj" => SchemeRelationRestriction.snd p q j

omit [Etale p] in
/-- Restricted coefficients satisfy the exact full original double-restriction equation. -/
theorem uniformSourceOpen_compatible (t : C) :
    (V).ι.appTop t.val ∈ SchemeEffectiveEpiSections.compatibleFunctions rj sj := by
  change (rj).appTop ((V).ι.appTop t.val) = (sj).appTop ((V).ι.appTop t.val)
  have h := uniformSourceOpen_test e I o U hU
    ((rj) ≫ (V).ι) ((sj) ≫ (V).ι) (SchemeRelationRestriction.arrow p q j)
    (by simpa only [Category.assoc] using SchemeRelationRestriction.arrow_fst p q j)
    (by simpa only [Category.assoc] using SchemeRelationRestriction.arrow_snd p q j)
    (by
      rintro _ ⟨x, rfl⟩
      exact ((rj) x).property) t
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using h

/-- Closedness of the actual bad image suffices to retain every complete source point. -/
theorem complete_mem_uniformSourceOpen_of_closed [IsLocallyNoetherian A]
    (hclosed : IsClosed ((r) '' (O : Set (SourceRestriction.relation U.ι U.ι))ᶜ))
    (x : U.toScheme) (hx : U.ι x ∈ completePointLocus (p := p) (q := q) I o) :
    x ∈ uniformSourceOpen e I o U hU := by
  apply SchemeOpenEnvelope.mem_fullFiberInterior_of_isClosed_image r O hclosed x
  intro y hy
  apply completeUniformRelationVanishingOpen_contains e I o U hU
  change U.ι ((r) y) ∈ completePointLocus (p := p) (q := q) I o
  rw [hy]
  exact hx

/-- Every previously complete interior point belongs to the constructed uniform source open. -/
theorem completeInterior_le_uniformSourceOpen [IsLocallyNoetherian A] :
    U.ι ⁻¹ᵁ completeInterior (p := p) (q := q) I o ≤ uniformSourceOpen e I o U hU := by
  apply (SchemeOpenEnvelope.le_fullFiberInterior_iff r O _).mpr
  intro y hy
  apply completeUniformRelationVanishingOpen_contains e I o U hU
  exact completeInterior_subset I o hy

end FLT.Mazur.EquivalenceRelationNormalizedFrames
