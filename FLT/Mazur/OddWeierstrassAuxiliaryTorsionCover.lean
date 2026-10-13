/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryTorsionDisjoint
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

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing)
open UniversalWeierstrass (Labels labels_pow)

/-- Each geometric point of the full torsion scheme lies on an actual label section. -/
theorem auxiliaryTorsionSection_geometric_factor
    (K : Type) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ auxiliaryThreeTorsion) :
    ∃ (a : Labels 3) (q : Spec (.of K) ⟶ levelThree.left), q ≫ auxiliaryTorsionSection a = p := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (p ≫ auxiliaryThreeTorsionMap ≫ levelThree.hom)
  let _ : Algebra OddChartRing K := r.hom.toAlgebra
  have hg : (fieldTest K).hom = p ≫ auxiliaryThreeTorsionMap ≫ levelThree.hom := hr
  let f : fieldTest K ⟶ levelThree := Over.homMk (p ≫ auxiliaryThreeTorsionMap) (by
    simpa only [Category.assoc] using hg.symm)
  let t : fieldTest K ⟶ threeTorsion :=
    Over.homMk (p ≫ pullback.fst threeTorsion.hom levelThree.hom) (by
      rw [Category.assoc, pullback.condition]
      exact hg.symm)
  let P := t ≫ GroupTorsionScheme.inclusion universalGroup 3
  have hP : P ^ 3 = 1 := by
    change (t ≫ GroupTorsionScheme.inclusion universalGroup 3) ^ 3 = 1
    rw [← MonObj.comp_pow, GroupTorsionScheme.inclusion_pow, MonObj.comp_one]
  obtain ⟨a, ha, _⟩ := levelThreeMarking_geometric_full K f P hP
  have ht : f ≫ auxiliaryTorsionMarking a = t := by
    apply equalizer.hom_ext
    change (f ≫ auxiliaryTorsionMarking a) ≫
      GroupTorsionScheme.inclusion universalGroup 3 = P
    rw [Category.assoc, auxiliaryTorsionMarking_inclusion]
    change (f ≫ levelThreeInclusion) ≫ AuxiliaryLevel.value universalGroup (Labels 3) a = P
      at ha
    change f ≫ (levelThreeInclusion ≫ AuxiliaryLevel.value universalGroup (Labels 3) a) = P
    exact (Category.assoc _ _ _).symm.trans ha
  refine ⟨a, p ≫ auxiliaryThreeTorsionMap, ?_⟩
  apply pullback.hom_ext
  · have ht' : (p ≫ auxiliaryThreeTorsionMap) ≫ (auxiliaryTorsionMarking a).left =
        p ≫ pullback.fst threeTorsion.hom levelThree.hom := congrArg Over.Hom.left ht
    simpa only [Category.assoc, auxiliaryTorsionSection_fst] using ht'
  · change ((p ≫ auxiliaryThreeTorsionMap) ≫ auxiliaryTorsionSection a) ≫
      auxiliaryThreeTorsionMap = p ≫ auxiliaryThreeTorsionMap
    simp only [Category.assoc, auxiliaryTorsionSection_map, Category.comp_id]

/-- The label sections cover the underlying full torsion scheme. -/
theorem auxiliaryTorsionSection_covers (x : auxiliaryThreeTorsion) :
    ∃ (a : Labels 3) (y : levelThree.left), auxiliaryTorsionSection a y = x :=
  GeometricPointCoverCriterion.covers auxiliaryTorsionSection
    auxiliaryTorsionSection_geometric_factor x

end FLT.Mazur.OddWeierstrassParameter
