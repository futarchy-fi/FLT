/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullRelation
public import FLT.Mazur.VariableHilbertChartRelation

/-!
# The original full chart relation inside the glued full relation

The actual full variable-chart relation maps to the constructed full relation.
Its endpoint square is cartesian: pulling back along both original chart
inclusions recovers the original relation, including distinct base maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V) (i : ι)
local notation "C" => baseMarkedGluedArrow f hL V a i
local notation "r₁" => variableChartRelationFst f hL (Prod.fst (a i)) V (Prod.snd (a i))
local notation "r₂" => variableChartRelationSnd f hL (Prod.fst (a i)) V (Prod.snd (a i))
local notation "p₁" => baseMarkedFullRelationFst f hL V a
local notation "p₂" => baseMarkedFullRelationSnd f hL V a

/-- The original full relation remains an equal-class pair in the glued scheme. -/
theorem baseMarkedOriginalRelation_class :
    baseMarkedGluedPoint f hL V a _ (r₁ ≫ C) =
      baseMarkedGluedPoint f hL V a _ (r₂ ≫ C) := by
  rw [baseMarkedGluedPoint_chart, baseMarkedGluedPoint_chart,
    ← variableChartSection_map, ← variableChartSection_map]
  exact variableChartRelation_class f hL (a i).1 V (a i).2

/-- Map the actual original full relation into the full relation of the glued scheme. -/
def baseMarkedOriginalRelationMap : variableChartRelation f hL (a i).1 V (a i).2 ⟶
    baseMarkedFullRelation f hL V a :=
  (baseMarkedFullRelation_lift f hL V a (r₁ ≫ C) (r₂ ≫ C)
    (baseMarkedOriginalRelation_class f hL V a i)).choose

@[reassoc]
theorem baseMarkedOriginalRelationMap_fst :
    baseMarkedOriginalRelationMap f hL V a i ≫ p₁ = r₁ ≫ C :=
  (baseMarkedFullRelation_lift f hL V a _ _
    (baseMarkedOriginalRelation_class f hL V a i)).choose_spec.1.1

@[reassoc]
theorem baseMarkedOriginalRelationMap_snd :
    baseMarkedOriginalRelationMap f hL V a i ≫ p₂ = r₂ ≫ C :=
  (baseMarkedFullRelation_lift f hL V a _ _
    (baseMarkedOriginalRelation_class f hL V a i)).choose_spec.1.2

/-- The endpoint square of the original full relation commutes. -/
theorem baseMarkedOriginalRelationMap_pair :
    baseMarkedOriginalRelationMap f hL V a i ≫ prod.lift p₁ p₂ =
      prod.lift r₁ r₂ ≫ prod.map C C := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc,
      baseMarkedOriginalRelationMap_fst]
  · simp only [Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc,
      baseMarkedOriginalRelationMap_snd]

/-- Pairs of original chart endpoints in the glued relation recover the original full relation. -/
theorem baseMarkedOriginalRelation_lift {W : Over (Spec (.of R))}
    (q : W ⟶ baseMarkedFullRelation f hL V a)
    (z : W ⟶ prod (variableHilbertTest f (a i).1 V) (variableHilbertTest f (a i).1 V))
    (he : q ≫ prod.lift p₁ p₂ = z ≫ prod.map C C) :
    ∃! l : W ⟶ variableChartRelation f hL (a i).1 V (a i).2,
      l ≫ baseMarkedOriginalRelationMap f hL V a i = q ∧ l ≫ prod.lift r₁ r₂ = z := by
  have h₁ : q ≫ p₁ = (z ≫ prod.fst) ≫ C := by
    simpa only [Category.assoc, prod.lift_fst, prod.map_fst] using
      congrArg (fun k ↦ k ≫ prod.fst) he
  have h₂ : q ≫ p₂ = (z ≫ prod.snd) ≫ C := by
    simpa only [Category.assoc, prod.lift_snd, prod.map_snd] using
      congrArg (fun k ↦ k ≫ prod.snd) he
  have hc : (relativeFppfSheaf f).obj.map (z ≫ prod.fst).op
      (variableChartSection f hL (a i).1 V (a i).2) =
        (relativeFppfSheaf f).obj.map (z ≫ prod.snd).op
          (variableChartSection f hL (a i).1 V (a i).2) := by
    rw [variableChartSection_map, variableChartSection_map,
      ← baseMarkedGluedPoint_chart, ← baseMarkedGluedPoint_chart, ← h₁, ← h₂,
      baseMarkedGluedPoint_natural, baseMarkedGluedPoint_natural, baseMarkedFullRelation_class]
  obtain ⟨l, hl, _⟩ := variableChartRelation_lift f hL (a i).1 V (a i).2
    (z ≫ prod.fst) (z ≫ prod.snd) hc
  have hq : l ≫ baseMarkedOriginalRelationMap f hL V a i = q := by
    apply baseMarkedFullRelation_hom_ext f hL V a
    · rw [Category.assoc, baseMarkedOriginalRelationMap_fst, ← Category.assoc, hl.1, h₁]
    · rw [Category.assoc, baseMarkedOriginalRelationMap_snd, ← Category.assoc, hl.2, h₂]
  have hz : l ≫ prod.lift r₁ r₂ = z := by
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using hl.1
    · simpa only [Category.assoc, prod.lift_snd] using hl.2
  refine ⟨l, ⟨hq, hz⟩, ?_⟩
  intro m hm
  apply variableChartRelation_hom_ext f hL (a i).1 V (a i).2
  · simpa only [Category.assoc, prod.lift_fst] using
      congrArg (fun k ↦ k ≫ prod.fst) (hm.2.trans hz.symm)
  · simpa only [Category.assoc, prod.lift_snd] using
      congrArg (fun k ↦ k ≫ prod.snd) (hm.2.trans hz.symm)

/-- The actual original full relation is the scheme pullback along both chart inclusions. -/
theorem baseMarkedOriginalRelation_isPullback :
    IsPullback (baseMarkedOriginalRelationMap f hL V a i) (prod.lift r₁ r₂)
      (prod.lift p₁ p₂) (prod.map C C) := by
  let lift (z : PullbackCone (prod.lift p₁ p₂) (prod.map C C)) :=
    baseMarkedOriginalRelation_lift f hL V a i z.fst z.snd z.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseMarkedOriginalRelationMap_pair f hL V a i) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2)
    (fun z q hq ht ↦ (lift z).choose_spec.2 q ⟨hq, ht⟩))

end FLT.Mazur.HilbertChart
