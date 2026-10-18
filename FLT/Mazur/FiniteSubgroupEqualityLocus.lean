/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSubgroupContainmentLocus
public import FLT.Mazur.CompatibleSubgroupIdealIso

/-!
# A scheme representing equality of actual finite subgroup ideals

Intersect the two constructed containment loci. The resulting closed base
scheme represents equality of the whole subgroup ideals after every base
change. At equal ranks this constructs an actual compatible subgroup
isomorphism on the universal family, with the original whole curve retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n m : ℕ}
  (H : E.FiniteSubgroup n) (J : E.FiniteSubgroup m)

/-- The actual intersection of both closed subgroup containment loci. -/
def equalityLocus : Scheme := pullback (containmentLocusInclusion H J)
  (containmentLocusInclusion J H)

/-- Its original closed map to the unchanged base. -/
def equalityLocusInclusion : equalityLocus H J ⟶ S :=
  pullback.fst (containmentLocusInclusion H J) (containmentLocusInclusion J H) ≫
    containmentLocusInclusion H J

instance equalityLocusInclusion_closed : IsClosedImmersion (equalityLocusInclusion H J) := by
  unfold equalityLocusInclusion
  infer_instance

/-- Tests factor through this closed scheme exactly when their full subgroup ideals agree. -/
theorem equalityLocus_factorization_iff {T : Scheme} (g : T ⟶ S) :
    (∃ k : T ⟶ equalityLocus H J, k ≫ equalityLocusInclusion H J = g) ↔
      (H.baseChange g).ideal = (J.baseChange g).ideal := by
  constructor
  · rintro ⟨k, hk⟩
    apply le_antisymm
    · apply (containmentLocus_factorization_iff J H g).mp
      refine ⟨k ≫ pullback.snd _ _, ?_⟩
      rw [Category.assoc, ← pullback.condition]
      exact hk
    · exact (containmentLocus_factorization_iff H J g).mp
        ⟨k ≫ pullback.fst _ _, by simpa only [equalityLocusInclusion, Category.assoc] using hk⟩
  · intro h
    obtain ⟨a, ha⟩ := (containmentLocus_factorization_iff H J g).mpr h.ge
    obtain ⟨b, hb⟩ := (containmentLocus_factorization_iff J H g).mpr h.le
    refine ⟨pullback.lift a b (ha.trans hb.symm), ?_⟩
    change pullback.lift a b _ ≫ pullback.fst _ _ ≫ containmentLocusInclusion H J = g
    rw [pullback.lift_fst_assoc, ha]

/-- The unique actual factorization associated with equality of pulled subgroup ideals. -/
def equalityLocusLift {T : Scheme} (g : T ⟶ S)
    (h : (H.baseChange g).ideal = (J.baseChange g).ideal) : T ⟶ equalityLocus H J :=
  ((equalityLocus_factorization_iff H J g).mpr h).choose

/-- Equality factorization retains the original parameter. -/
@[reassoc] theorem equalityLocusLift_inclusion {T : Scheme} (g : T ⟶ S)
    (h : (H.baseChange g).ideal = (J.baseChange g).ideal) :
    equalityLocusLift H J g h ≫ equalityLocusInclusion H J = g :=
  ((equalityLocus_factorization_iff H J g).mpr h).choose_spec

/-- The representing closed immersion determines the factorization uniquely. -/
theorem equalityLocusLift_unique {T : Scheme} (g : T ⟶ S)
    (h : (H.baseChange g).ideal = (J.baseChange g).ideal) (k : T ⟶ equalityLocus H J)
    (hk : k ≫ equalityLocusInclusion H J = g) : k = equalityLocusLift H J g h := by
  apply (cancel_mono (equalityLocusInclusion H J)).mp
  rw [hk, equalityLocusLift_inclusion]

/-- The whole universal pulled subgroup ideals actually agree on the constructed scheme. -/
theorem equalityLocus_universal_ideal :
    (H.baseChange (equalityLocusInclusion H J)).ideal =
      (J.baseChange (equalityLocusInclusion H J)).ideal :=
  (equalityLocus_factorization_iff H J _).mp ⟨𝟙 _, Category.id_comp _⟩

variable (K : E.FiniteSubgroup n)

/-- Equality of the universal ideals constructs a genuine full compatible comparison. -/
def equalityLocusCompatibleIso : CompatibleIso (H.baseChange (equalityLocusInclusion H K))
    (K.baseChange (equalityLocusInclusion H K)) :=
  compatibleIsoOfIdealEq _ _ (equalityLocus_universal_ideal H K)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
