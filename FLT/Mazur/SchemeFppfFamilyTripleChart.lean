/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFamilyTripleOverlap
public import FLT.Mazur.SchemeFppfFamilyOverlapCover

/-!
# Original triple charts in the total family overlap

Each triple of original members maps into the actual triple overlap of the
coproduct covering map. All three original pair projections are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- The adjacent-pair triple overlap of three original members. -/
abbrev tripleChart (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) : Scheme.{u} :=
  SchemeFamilyTripleOverlap.triple (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2)

/-- The first-pair inclusion commutes with the map to the base. -/
@[reassoc]
lemma pairMap_base (ij : 𝒰.I₀ × 𝒰.I₀) :
    pairMap 𝒰 ij ≫ (Limits.pullback.snd (projection 𝒰) (projection 𝒰) ≫ projection 𝒰) =
      Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) ≫ 𝒰.f ij.2 := by
  rw [← Category.assoc, pairMap_snd, Category.assoc, inclusion_projection]

/-- The triple chart map expressed via the pasted fiber products over the base. -/
def tripleChartMap (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    tripleChart 𝒰 ijk ⟶ SchemeTripleOverlap.triple (projection 𝒰) :=
  (SchemeFamilyTripleOverlap.pasteIso (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2)).hom ≫
    Limits.pullback.map _ _ _ _ (pairMap 𝒰 ijk.1) (Limits.Sigma.ι 𝒰.X ijk.2)
      (𝟙 X) (by simp only [Category.comp_id, pairMap_base]) (by simp) ≫
    (SchemeFamilyTripleOverlap.pasteIso (projection 𝒰) (projection 𝒰) (projection 𝒰)).inv

instance tripleChartMap_isOpenImmersion (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    IsOpenImmersion (tripleChartMap 𝒰 ijk) := by
  unfold tripleChartMap
  infer_instance

@[reassoc (attr := simp)]
lemma tripleChartMap_pair12 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.pair12 (projection 𝒰) =
      SchemeFamilyTripleOverlap.pair12 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2) ≫
        pairMap 𝒰 ijk.1 := by
  change tripleChartMap 𝒰 ijk ≫
    SchemeFamilyTripleOverlap.pair12 (projection 𝒰) (projection 𝒰) (projection 𝒰) = _
  simp only [tripleChartMap, Category.assoc, SchemeFamilyTripleOverlap.pasteIso_inv_pair12,
    Limits.pullback.map, Limits.pullback.lift_fst,
    SchemeFamilyTripleOverlap.pasteIso_hom_fst_assoc]

@[reassoc]
lemma tripleChartMap_coord1 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord1 (projection 𝒰) =
      SchemeFamilyTripleOverlap.coord1 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2) ≫
        Limits.Sigma.ι 𝒰.X ijk.1.1 := by
  simp only [SchemeTripleOverlap.coord1, tripleChartMap_pair12_assoc,
    pairMap_fst, Category.assoc, SchemeFamilyTripleOverlap.coord1]

@[reassoc]
lemma tripleChartMap_coord2 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord2 (projection 𝒰) =
      SchemeFamilyTripleOverlap.coord2 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2) ≫
        Limits.Sigma.ι 𝒰.X ijk.1.2 := by
  simp only [SchemeTripleOverlap.coord2, tripleChartMap_pair12_assoc,
    pairMap_snd, Category.assoc, SchemeFamilyTripleOverlap.coord2]

@[reassoc]
lemma tripleChartMap_coord3 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord3 (projection 𝒰) =
      SchemeFamilyTripleOverlap.coord3 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2) ≫
        Limits.Sigma.ι 𝒰.X ijk.2 := by
  change tripleChartMap 𝒰 ijk ≫
    SchemeFamilyTripleOverlap.coord3 (projection 𝒰) (projection 𝒰) (projection 𝒰) = _
  simp only [tripleChartMap, Category.assoc, SchemeFamilyTripleOverlap.pasteIso_inv_coord3,
    Limits.pullback.map, Limits.pullback.lift_snd,
    SchemeFamilyTripleOverlap.pasteIso_hom_snd_assoc]

@[reassoc (attr := simp)]
lemma tripleChartMap_pair23 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.pair23 (projection 𝒰) =
      SchemeFamilyTripleOverlap.pair23 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2) ≫
        pairMap 𝒰 (ijk.1.2, ijk.2) := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, SchemeTripleOverlap.pair23_fst, pairMap_fst]
    rw [tripleChartMap_coord2, ← Category.assoc, SchemeFamilyTripleOverlap.pair23_fst]
  · simpa only [Category.assoc, pairMap_snd] using tripleChartMap_coord3 𝒰 ijk

@[reassoc (attr := simp)]
lemma tripleChartMap_pair13 (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.pair13 (projection 𝒰) =
      SchemeFamilyTripleOverlap.pair13 (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2) ≫
        pairMap 𝒰 (ijk.1.1, ijk.2) := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, SchemeTripleOverlap.pair13_fst, pairMap_fst,
      SchemeFamilyTripleOverlap.pair13_fst_assoc, tripleChartMap_coord1]
  · simp only [Category.assoc, SchemeTripleOverlap.pair13_snd, pairMap_snd,
      SchemeFamilyTripleOverlap.pair13_snd_assoc, tripleChartMap_coord3]

end FLT.Mazur.SchemeFppfFamily
