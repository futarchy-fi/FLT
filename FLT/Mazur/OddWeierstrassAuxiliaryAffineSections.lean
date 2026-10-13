/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricOpenFactorization
public import FLT.Mazur.OddWeierstrassAuxiliaryEtale
public import FLT.Mazur.WeierstrassNonzeroPointAffine

/-!
# Nonzero auxiliary markings are actual affine sections

Every nonidentity label factors through the original affine chart of the
universal cubic, over the entire auxiliary level scheme. The geometric test
proves open containment and therefore preserves all nonreduced base data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels)

open WeierstrassIntegralChart

/-- Nonidentity labels are affine on every geometric test of the actual auxiliary cover. -/
theorem auxiliaryMarking_geometric_affine (a : Labels 3) (ha : a ≠ 1)
    (K : Type) [Field K] (p : Spec (.of K) ⟶ levelThree.left) :
    ∃ q : Spec (.of K) ⟶ chartScheme oddChartEquation 2,
      q ≫ integralCurveChart oddChartEquation 2 = p ≫ (levelThreeMarking a).left := by
  classical
  obtain ⟨r, hr⟩ := Spec.map_surjective (p ≫ levelThree.hom)
  let _ : Algebra OddChartRing K := r.hom.toAlgebra
  let f : fieldTest K ⟶ levelThree := Over.homMk p hr.symm
  let _ : Nonempty (fieldTest K).left := ⟨IsLocalRing.closedPoint K⟩
  let φ := AuxiliaryLevel.markingOf universalGroup (Labels 3) (f ≫ levelThreeInclusion)
  have hn : φ a ≠ 1 := by
    intro h
    exact ha (levelThreeMarking_injective f (h.trans φ.map_one.symm))
  obtain ⟨q, hq⟩ := nonzeroPoint_factor oddChartEquation oddChart_discriminant (φ a) hn
  refine ⟨q, hq.trans ?_⟩
  exact congrArg Over.Hom.left (AuxiliaryLevel.markingOf_comp _ _ f (levelThreeInclusion) a)

/-- Every nonidentity section lies in the original affine chart, including over nilpotents. -/
theorem auxiliaryMarking_affine_range (a : Labels 3) (ha : a ≠ 1) :
    Set.range (levelThreeMarking a).left ⊆ Set.range (integralCurveChart oddChartEquation 2) :=
  GeometricOpenFactorization.range_subset _ _
    (fun K _ _ p ↦ auxiliaryMarking_geometric_affine a ha K p)

/-- The actual affine chart lift of a nonidentity auxiliary marking. -/
def auxiliaryAffineSection (a : Labels 3) (ha : a ≠ 1) :
    levelThree.left ⟶ chartScheme oddChartEquation 2 :=
  IsOpenImmersion.lift (integralCurveChart oddChartEquation 2) (levelThreeMarking a).left
    (auxiliaryMarking_affine_range a ha)

/-- The affine lift recovers exactly the original marked section of the universal curve. -/
@[reassoc (attr := simp)] theorem auxiliaryAffineSection_inclusion (a : Labels 3) (ha : a ≠ 1) :
    auxiliaryAffineSection a ha ≫ integralCurveChart oddChartEquation 2 =
      (levelThreeMarking a).left := IsOpenImmersion.lift_fac _ _ _

/-- The affine lift retains the original auxiliary coefficient map. -/
@[reassoc (attr := simp)] theorem auxiliaryAffineSection_base (a : Labels 3) (ha : a ≠ 1) :
    auxiliaryAffineSection a ha ≫ chartStructure oddChartEquation 2 = levelThree.hom := by
  rw [← integralCurveChart_structure, ← Category.assoc, auxiliaryAffineSection_inclusion]
  exact (levelThreeMarking a).w

end FLT.Mazur.OddWeierstrassParameter
