/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonFieldFibers
public import FLT.Mazur.OneGonSmoothingGenusOneFamily

/-!
# Classified genus-one degeneration families over arithmetic rings

The actual proper flat cubic is a classified genus-one family whenever the
complementary discriminant factor is invertible. In particular this constructs
such a family over R[[t]] for every ring R, including mixed characteristic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonFamily

open OneGonSmoothing ArithmeticOneGonFieldFibers FCurve FCurve.CurveFiberHypotheses
open FCurve.DRFiberClassification

variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))

include ht in
/-- Every geometric fiber is smooth or the original pinched one-gon. -/
theorem classifiedGeometricFibers : ClassifiedGeometricFibers (family t).hom :=
  ⟨fun L _ _ s _ p q hs ↦ cartesian_classified t ht L s p q hs⟩

include ht in
/-- The actual geometric fibers retain their nodal core, constants, and first cohomology. -/
theorem genusOneGeometricFibers :
    let _ := family_proper t
    NodalGenusOneGeometricFibers (family t).hom := by
  let _ := family_proper t
  constructor
  intro L _ _ s Y p q hs
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  exact ⟨(cartesian_classified t ht L s p q hs).toNodalFiberCore,
    cartesian_constantSections t L s p q hs, cartesianH1_finrank t L s p q hs⟩

include ht in
/-- The original arithmetic degeneration satisfies the full classified genus-one contract. -/
theorem classifiedGenusOneFamily : ClassifiedGenusOneFamily (family t).hom :=
  ⟨⟨family_proper t, family_flat t, family_lfp t⟩,
    classifiedGeometricFibers t ht, genusOneGeometricFibers t ht⟩

include ht in
/-- Arbitrary scheme tests retain the original arithmetic family and all its fiber contracts. -/
theorem baseChange_classifiedGenusOneFamily {S : Scheme} (s : S ⟶ Spec (.of R)) :
    ClassifiedGenusOneFamily (pullback.snd (family t).hom s) :=
  (classifiedGenusOneFamily t ht).baseChange s

/-- The complete parameter family exists over every coefficient ring. -/
theorem powerSeries_classifiedGenusOneFamily (A : Type) [CommRing A] :
    ClassifiedGenusOneFamily (family (PowerSeries.X : PowerSeries A)).hom :=
  classifiedGenusOneFamily _ powerSeries_discriminant_factor_unit

/-- The arithmetic family over the integers includes all residue characteristics. -/
theorem integralPowerSeries_classifiedGenusOneFamily :
    ClassifiedGenusOneFamily (family (PowerSeries.X : PowerSeries ℤ)).hom :=
  powerSeries_classifiedGenusOneFamily ℤ

end FLT.Mazur.ArithmeticOneGonFamily
