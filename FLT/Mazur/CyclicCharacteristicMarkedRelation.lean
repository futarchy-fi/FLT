/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicNormalizedAtlas
public import FLT.Mazur.CyclicHomGlobalMarkedRelation
public import FLT.Mazur.OddWeierstrassCyclicHomGlobalMarkedRelation

/-!
# Represented marked relations on both characteristic charts

The actual normalization kernel pairs represent genuine independent marked
comparisons on arbitrary test schemes. Both original subgroup parameters are
retained by the projections; no affine hypothesis is placed on the source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]

/-- The actual normalization kernel pair on either characteristic chart. -/
def markedRelation (b : Bool) : Scheme := pullback (normalization n b) (normalization n b)

/-- The first original subgroup parameter retained by a marked comparison. -/
def markedRelationFirst (b : Bool) : markedRelation n b ⟶ locus n b := pullback.fst _ _

/-- The second original subgroup parameter retained by a marked comparison. -/
def markedRelationSecond (b : Bool) : markedRelation n b ⟶ locus n b := pullback.snd _ _

/-- The represented marked relation equates the actual normalized parameters. -/
@[reassoc] theorem markedRelation_condition (b : Bool) :
    markedRelationFirst n b ≫ normalization n b =
      markedRelationSecond n b ≫ normalization n b := pullback.condition

/-- The relation predicate uses actual group comparisons preserving both original markings. -/
def MarkedRelated : (b : Bool) → {T : Scheme} → (T ⟶ locus n b) → (T ⟶ locus n b) → Prop
  | false, _, f, g => UniversalWeierstrass.CyclicHomMarkedFamilyRelated n
      (f ≫ UniversalWeierstrass.cyclicHomUniversalMultiplicationLocusInclusion n)
      (g ≫ UniversalWeierstrass.cyclicHomUniversalMultiplicationLocusInclusion n)
  | true, _, f, g => OddWeierstrassParameter.CyclicHomMarkedFamilyRelated n
      (f ≫ OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocusInclusion n)
      (g ≫ OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocusInclusion n)

/-- On both charts arbitrary-source marked comparison is precisely kernel-pair membership. -/
theorem markedRelated_iff_normalization_eq (b : Bool) {T : Scheme}
    (f g : T ⟶ locus n b) :
    MarkedRelated n b f g ↔ f ≫ normalization n b = g ≫ normalization n b := by
  cases b
  · exact (UniversalWeierstrass.cyclicHomLocusRelation_iff_global_marked n f g).symm
  · exact (OddWeierstrassParameter.cyclicHomLocusRelation_iff_global_marked n f g).symm

/-- Actual marked comparisons give points of the represented relation. -/
def markedRelationPoint (b : Bool) {T : Scheme} (f g : T ⟶ locus n b)
    (h : MarkedRelated n b f g) : T ⟶ markedRelation n b :=
  pullback.lift f g ((markedRelated_iff_normalization_eq n b f g).mp h)

/-- A represented comparison retains its specified original source. -/
@[reassoc] theorem markedRelationPoint_first (b : Bool) {T : Scheme}
    (f g : T ⟶ locus n b) (h : MarkedRelated n b f g) :
    markedRelationPoint n b f g h ≫ markedRelationFirst n b = f := pullback.lift_fst _ _ _

/-- A represented comparison retains its specified original target. -/
@[reassoc] theorem markedRelationPoint_second (b : Bool) {T : Scheme}
    (f g : T ⟶ locus n b) (h : MarkedRelated n b f g) :
    markedRelationPoint n b f g h ≫ markedRelationSecond n b = g := pullback.lift_snd _ _ _

/-- The two retained original parameters determine the represented comparison point uniquely. -/
theorem markedRelation_hom_ext (b : Bool) {T : Scheme} (f g : T ⟶ markedRelation n b)
    (h₁ : f ≫ markedRelationFirst n b = g ≫ markedRelationFirst n b)
    (h₂ : f ≫ markedRelationSecond n b = g ≫ markedRelationSecond n b) : f = g :=
  pullback.hom_ext h₁ h₂

/-- Every represented relation point supplies the genuine original marked comparison. -/
theorem markedRelationPoint_related (b : Bool) {T : Scheme} (q : T ⟶ markedRelation n b) :
    MarkedRelated n b (q ≫ markedRelationFirst n b) (q ≫ markedRelationSecond n b) := by
  apply (markedRelated_iff_normalization_eq n b _ _).mpr
  simp only [Category.assoc, markedRelation_condition]

end FLT.Mazur.CyclicCharacteristicAtlas
