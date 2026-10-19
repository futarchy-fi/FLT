/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSubgroupComparisonBaseChangeCriterion

/-!
# Actual base change of the closed subgroup comparison locus

The closed locus of a restricted full comparison is the scheme pullback of
the original closed locus. The map and both projections are constructed
from the factorization criterion on arbitrary scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n) (e : E ≅ F) (g : T ⟶ S)
local notation "e'" => Functor.mapIso (baseChangeFunctor g) e
local notation "i" => subgroupComparisonLocusInclusion H J e
local notation "i'" => subgroupComparisonLocusInclusion (H.baseChange g) (J.baseChange g) e'

/-- The restricted locus has a canonical map to the original closed subgroup locus. -/
def subgroupComparisonLocusBaseChangeMap :
    subgroupComparisonLocus (H.baseChange g) (J.baseChange g) e' ⟶
      subgroupComparisonLocus H J e :=
  ((subgroupComparisonLocus_factorization_baseChange_iff H J e g i').mp
    ⟨𝟙 _, Category.id_comp _⟩).choose

/-- The constructed comparison-locus map keeps its original base map. -/
@[reassoc] theorem subgroupComparisonLocusBaseChangeMap_inclusion :
    subgroupComparisonLocusBaseChangeMap H J e g ≫ i = i' ≫ g :=
  ((subgroupComparisonLocus_factorization_baseChange_iff H J e g i').mp
    ⟨𝟙 _, Category.id_comp _⟩).choose_spec

/-- The original and restricted closed comparison loci form an actual pullback square. -/
theorem subgroupComparisonLocusBaseChange_isPullback :
    IsPullback i' (subgroupComparisonLocusBaseChangeMap H J e g) g i := by
  apply IsPullback.mk' (subgroupComparisonLocusBaseChangeMap_inclusion H J e g).symm
  · intro U a b ha _
    exact (cancel_mono i').mp ha
  · intro U a b hab
    obtain ⟨l, hl⟩ :=
      (subgroupComparisonLocus_factorization_baseChange_iff H J e g a).mpr ⟨b, hab.symm⟩
    refine ⟨l, hl, ?_⟩
    apply (cancel_mono i).mp
    rw [Category.assoc, subgroupComparisonLocusBaseChangeMap_inclusion,
      ← Category.assoc, hl, hab]

/-- Restricting a prescribed full comparison pulls back its entire closed subgroup locus. -/
def subgroupComparisonLocusBaseChangeIso :
    subgroupComparisonLocus (H.baseChange g) (J.baseChange g) e' ≅ pullback g i :=
  (subgroupComparisonLocusBaseChange_isPullback H J e g).isoPullback

/-- The pullback identification retains the restricted closed immersion. -/
@[reassoc] theorem subgroupComparisonLocusBaseChangeIso_fst :
    (subgroupComparisonLocusBaseChangeIso H J e g).hom ≫ pullback.fst _ _ = i' :=
  (subgroupComparisonLocusBaseChange_isPullback H J e g).isoPullback_hom_fst

/-- The other projection is the constructed map of closed comparison schemes. -/
@[reassoc] theorem subgroupComparisonLocusBaseChangeIso_snd :
    (subgroupComparisonLocusBaseChangeIso H J e g).hom ≫ pullback.snd _ _ =
      subgroupComparisonLocusBaseChangeMap H J e g :=
  (subgroupComparisonLocusBaseChange_isPullback H J e g).isoPullback_hom_snd

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
