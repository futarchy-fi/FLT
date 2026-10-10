/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryTorsionDisjoint
public import FLT.Mazur.GeometricPointCoverCriterion

/-!
# The auxiliary torsion sections cover the full torsion scheme

Geometric fullness factors every algebraically closed field-valued point
through an actual marked section. Residue-field geometric points then prove
coverage, including points of nonreduced test bases.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

/-- Each geometric point of the full torsion scheme lies on an actual label section. -/
theorem auxiliaryTorsionSection_geometric_factor
    (K : Type) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ auxiliaryFourTorsion) :
    ∃ (a : Labels 4) (q : Spec (.of K) ⟶ levelFour.left), q ≫ auxiliaryTorsionSection a = p := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (p ≫ auxiliaryFourTorsionMap ≫ levelFour.hom)
  let _ : Algebra ParameterRing K := r.hom.toAlgebra
  have hg : (fieldTest K).hom = p ≫ auxiliaryFourTorsionMap ≫ levelFour.hom := hr
  let f : fieldTest K ⟶ levelFour := Over.homMk (p ≫ auxiliaryFourTorsionMap) (by
    simpa only [Category.assoc] using hg.symm)
  let t : fieldTest K ⟶ fourTorsion :=
    Over.homMk (p ≫ pullback.fst fourTorsion.hom levelFour.hom) (by
      rw [Category.assoc, pullback.condition]
      exact hg.symm)
  let P := t ≫ GroupTorsionScheme.inclusion universalGroup 4
  have hP : P ^ 4 = 1 := by
    change (t ≫ GroupTorsionScheme.inclusion universalGroup 4) ^ 4 = 1
    rw [← MonObj.comp_pow, GroupTorsionScheme.inclusion_pow, MonObj.comp_one]
  obtain ⟨a, ha, _⟩ := auxiliaryMarking_geometric_full K f P hP
  have ht : f ≫ auxiliaryTorsionMarking a = t := by
    apply equalizer.hom_ext
    change (f ≫ auxiliaryTorsionMarking a) ≫
      GroupTorsionScheme.inclusion universalGroup 4 = P
    rw [Category.assoc, auxiliaryTorsionMarking_inclusion]
    change (f ≫ auxiliaryInclusion 4) ≫ AuxiliaryLevel.value universalGroup (Labels 4) a = P
      at ha
    change f ≫ (auxiliaryInclusion 4 ≫ AuxiliaryLevel.value universalGroup (Labels 4) a) = P
    exact (Category.assoc _ _ _).symm.trans ha
  refine ⟨a, p ≫ auxiliaryFourTorsionMap, ?_⟩
  apply pullback.hom_ext
  · have ht' : (p ≫ auxiliaryFourTorsionMap) ≫ (auxiliaryTorsionMarking a).left =
        p ≫ pullback.fst fourTorsion.hom levelFour.hom := congrArg Over.Hom.left ht
    simpa only [Category.assoc, auxiliaryTorsionSection_fst] using ht'
  · change ((p ≫ auxiliaryFourTorsionMap) ≫ auxiliaryTorsionSection a) ≫
      auxiliaryFourTorsionMap = p ≫ auxiliaryFourTorsionMap
    simp only [Category.assoc, auxiliaryTorsionSection_map, Category.comp_id]

/-- The label sections cover the underlying full torsion scheme. -/
theorem auxiliaryTorsionSection_covers (x : auxiliaryFourTorsion) :
    ∃ (a : Labels 4) (y : levelFour.left), auxiliaryTorsionSection a y = x :=
  GeometricPointCoverCriterion.covers auxiliaryTorsionSection
    auxiliaryTorsionSection_geometric_factor x

end FLT.Mazur.UniversalWeierstrass
