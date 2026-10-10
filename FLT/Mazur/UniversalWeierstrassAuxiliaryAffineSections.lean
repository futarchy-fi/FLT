/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricOpenFactorization
public import FLT.Mazur.UniversalWeierstrassAuxiliaryEtale
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

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

/-- Nonidentity labels are affine on every geometric test of the actual auxiliary cover. -/
theorem auxiliaryMarking_geometric_affine (a : Labels 4) (ha : a ≠ 1)
    (K : Type) [Field K] (p : Spec (.of K) ⟶ levelFour.left) :
    ∃ q : Spec (.of K) ⟶ chartScheme smoothEquation 2,
      q ≫ integralCurveChart smoothEquation 2 = p ≫ (auxiliaryMarking 4 a).left := by
  classical
  obtain ⟨r, hr⟩ := Spec.map_surjective (p ≫ levelFour.hom)
  let _ : Algebra ParameterRing K := r.hom.toAlgebra
  let f : fieldTest K ⟶ levelFour := Over.homMk p hr.symm
  let _ : Nonempty (fieldTest K).left := ⟨IsLocalRing.closedPoint K⟩
  let φ := AuxiliaryLevel.markingOf universalGroup (Labels 4) (f ≫ auxiliaryInclusion 4)
  have hn : φ a ≠ 1 := by
    intro h
    exact ha (auxiliaryMarking_injective 4 f (h.trans φ.map_one.symm))
  obtain ⟨q, hq⟩ := nonzeroPoint_factor smoothEquation smoothEquation_discriminant (φ a) hn
  refine ⟨q, hq.trans ?_⟩
  exact congrArg Over.Hom.left (AuxiliaryLevel.markingOf_comp _ _ f (auxiliaryInclusion 4) a)

/-- Every nonidentity section lies in the original affine chart, including over nilpotents. -/
theorem auxiliaryMarking_affine_range (a : Labels 4) (ha : a ≠ 1) :
    Set.range (auxiliaryMarking 4 a).left ⊆ Set.range (integralCurveChart smoothEquation 2) :=
  GeometricOpenFactorization.range_subset _ _
    (fun K _ _ p ↦ auxiliaryMarking_geometric_affine a ha K p)

/-- The actual affine chart lift of a nonidentity auxiliary marking. -/
def auxiliaryAffineSection (a : Labels 4) (ha : a ≠ 1) :
    levelFour.left ⟶ chartScheme smoothEquation 2 :=
  IsOpenImmersion.lift (integralCurveChart smoothEquation 2) (auxiliaryMarking 4 a).left
    (auxiliaryMarking_affine_range a ha)

/-- The affine lift recovers exactly the original marked section of the universal curve. -/
@[reassoc (attr := simp)] theorem auxiliaryAffineSection_inclusion (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryAffineSection a ha ≫ integralCurveChart smoothEquation 2 =
      (auxiliaryMarking 4 a).left := IsOpenImmersion.lift_fac _ _ _

/-- The affine lift retains the original auxiliary coefficient map. -/
@[reassoc (attr := simp)] theorem auxiliaryAffineSection_base (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryAffineSection a ha ≫ chartStructure smoothEquation 2 = levelFour.hom := by
  rw [← integralCurveChart_structure, ← Category.assoc, auxiliaryAffineSection_inclusion]
  exact (auxiliaryMarking 4 a).w

end FLT.Mazur.UniversalWeierstrass
