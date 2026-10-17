/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomNormalizationSubgroupMarking
public import FLT.Mazur.CartierGeneratorOrbitRecovery

/-!
# Normalized parameters retain an originally specified generator

An original subgroup with the source orbit ideal is compared with the actual
normalized source subgroup. The prescribed original marking determines the
chosen normalized Cartier generator under this full compatible comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)
  (J : (cyclicHomSourceCurve n f).FiniteSubgroup n)
  (hJ : J.ideal = cyclicHomSourceIdeal n f)

/-- The original source subgroup is compared by equality of its full orbit ideal. -/
def cyclicHomPrescribedSubgroupIso : CompatibleIso (cyclicHomSubgroup n f h) J :=
  compatibleIsoOfIdealEq _ _ ((cyclicHomSubgroup_ideal n f h).trans hJ.symm)

variable {P : 𝟙_ (Over T) ⟶ J.carrier} (hP : J.IsCartierGenerator P)
  (hφ : J.generatorCurveMarking hP = cyclicHomSourceMarking n f)

include hφ in
/-- The source comparison carries the chosen orbit generator to the prescribed original. -/
theorem cyclicHomPrescribedSubgroupIso_generator :
    (cyclicHomSubgroup n f h).orbitGenerator (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f h) ≫ (cyclicHomPrescribedSubgroupIso n f h J hJ).subgroup.hom =
        P := by
  rw [← J.orbitGenerator_eq_of_generatorMarking hP _ hJ hφ]
  apply CompatibleIso.orbitGenerator_eq
  exact Category.comp_id _

/-- Normalize while retaining the actual original subgroup carrier and whole curve. -/
def cyclicHomNormalizedPrescribedSubgroupIso :
    CompatibleIso (cyclicHomSubgroup n (cyclicHomNormalizedPoint n f)
      (cyclicHomNormalization_equation n f h)) J :=
  (cyclicHomNormalizationSubgroupIso n f h).trans (cyclicHomPrescribedSubgroupIso n f h J hJ)

include hφ in
/-- The chosen normalized generator is precisely the prescribed original Cartier generator. -/
theorem cyclicHomNormalizedPrescribedSubgroupIso_generator :
    (cyclicHomSubgroup n (cyclicHomNormalizedPoint n f)
      (cyclicHomNormalization_equation n f h)).orbitGenerator
        (cyclicHomSourceMarking n (cyclicHomNormalizedPoint n f))
        (cyclicHomSubgroup_ideal n _ _) ≫
          (cyclicHomNormalizedPrescribedSubgroupIso n f h J hJ).subgroup.hom = P := by
  change _ ≫ ((cyclicHomNormalizationSubgroupIso n f h).subgroup.hom ≫
    (cyclicHomPrescribedSubgroupIso n f h J hJ).subgroup.hom) = _
  rw [← Category.assoc, cyclicHomNormalizationSubgroupIso_generator]
  exact cyclicHomPrescribedSubgroupIso_generator n f h J hJ hP hφ

end FLT.Mazur.UniversalWeierstrass
