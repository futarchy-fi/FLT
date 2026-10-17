/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationGroup

/-!
# Normalization retains the entire cyclic Cartier subgroup

The full curve comparison preserves the product ideal with every repeated
factor. Transporting the actual original subgroup therefore proves the
normalized multiplication equation, without a distinctness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "fN" => cyclicHomNormalizedPoint n f

/-- Normalization compares the whole smooth source curves. -/
def cyclicHomNormalizationCurveIso : cyclicHomSourceCurve n fN ≅ cyclicHomSourceCurve n f := by
  let e : (cyclicHomSourceCurve n fN).group ≅ (cyclicHomSourceCurve n f).group :=
    (CommGrp.forget _).mapIso (cyclicHomNormalizationGroupIso n f)
  let _ : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (cyclicHomNormalizationGroupIso n f).hom.hom.hom.hom)
  let _ : Smooth (cyclicHomSourceCurve n f).curve.hom :=
    SmoothOfRelativeDimension.smooth 1 _
  let _ : Smooth (cyclicHomSourceCurve n fN).curve.hom :=
    SmoothOfRelativeDimension.smooth 1 _
  exact isoOfSmoothGroup _ _ e

/-- The normalized orbit ideal retains all factors of the original ideal. -/
theorem cyclicHomNormalization_ideal :
    cyclicHomSourceIdeal n fN =
      (cyclicHomSourceIdeal n f).comap (cyclicHomNormalizationCurveIso n f).hom.curve.left := by
  have hm (i : Multiplicative (ZMod n)) :
      cyclicHomSourceMarking n f i ≫ (cyclicHomNormalizationCurveIso n f).inv.group =
        cyclicHomSourceMarking n fN i := by
    rw [← cyclicHomNormalizationGroupIso_marking n f i]
    change (_ ≫ (groupIso (cyclicHomNormalizationCurveIso n f)).hom) ≫
      (groupIso (cyclicHomNormalizationCurveIso n f)).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact cyclicMarkingIdeal_transport (cyclicHomSourceMarking n f)
    (cyclicHomSourceMarking n fN) (cyclicHomNormalizationCurveIso n f).symm hm

variable (h : cyclicHomMultiplicationEquation n f = 0)

/-- Transporting the original subgroup gives precisely the normalized orbit ideal. -/
theorem cyclicHomNormalization_retained_ideal :
    ((cyclicHomSubgroup n f h).transport (cyclicHomNormalizationCurveIso n f).symm).ideal =
      cyclicHomSourceIdeal n fN := by
  let H := cyclicHomSubgroup n f h
  let a := H.transportCompatibleIso (cyclicHomNormalizationCurveIso n f).symm
  have hi := ideal_transport H _ a.curve a.subgroup a.compatible
  change _ = H.ideal.comap (cyclicHomNormalizationCurveIso n f).hom.curve.left at hi
  rw [show H.ideal = cyclicHomSourceIdeal n f from cyclicHomSubgroup_ideal n f h] at hi
  exact hi.trans (cyclicHomNormalization_ideal n f).symm

include h in
/-- Every original subgroup parameter normalizes to another actual subgroup parameter. -/
theorem cyclicHomNormalization_equation : cyclicHomMultiplicationEquation n fN = 0 :=
  cyclicHomMultiplicationEquation_of_subgroup n fN
    ((cyclicHomSubgroup n f h).transport (cyclicHomNormalizationCurveIso n f).symm)
    (cyclicHomNormalization_retained_ideal n f h)

/-- The full normalized subgroup is compatibly isomorphic to the full original subgroup. -/
def cyclicHomNormalizationSubgroupIso :
    CompatibleIso (cyclicHomSubgroup n fN (cyclicHomNormalization_equation n f h))
      (cyclicHomSubgroup n f h) :=
  (compatibleIsoOfIdealEq _ _ ((cyclicHomSubgroup_ideal n _ _).trans
    (cyclicHomNormalization_retained_ideal n f h).symm)).trans
      ((cyclicHomSubgroup n f h).transportCompatibleIso
        (cyclicHomNormalizationCurveIso n f).symm).symm

/-- Normalization preserves the actual ample cyclic modular class. -/
theorem cyclicHomSourceModuliClass_normalization :
    cyclicHomSourceModuliClass n fN (cyclicHomNormalization_equation n f h) =
      cyclicHomSourceModuliClass n f h :=
  Quotient.sound ⟨cyclicHomNormalizationSubgroupIso n f h⟩

end FLT.Mazur.OddWeierstrassParameter
