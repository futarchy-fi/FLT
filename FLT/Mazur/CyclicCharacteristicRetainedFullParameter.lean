/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRetainedParameter
public import FLT.Mazur.AuxiliaryCyclicProductParameter
public import FLT.Mazur.CartierGeneratorMarkedSubgroup
public import FLT.Mazur.EtaleCartierGeneratorDistinct

/-!
# Faithful full parameters on retained etale cyclic subgroups

When the original subgroup is etale, its prescribed Cartier generator has
universally distinct powers. Coprimality with the characteristic chart's
auxiliary order then gives a faithful product parameter retaining both factors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open AuxiliaryLevel
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}

/-- Separation of the original group used by the faithful full parameter. -/
local instance retainedFullParameterGroupSeparated : IsSeparated E.group.hom := by
  let _ : IsProper E.curve.hom := E.family.family.1
  rw [← E.inclusion.w]
  infer_instance

variable {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) [Etale H.carrier.hom]
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

/-- The original etale Cartier generator defines an actual faithful cyclic parameter. -/
def retainedEtaleCyclicParameter :
    𝟙_ (Over S) ⟶ faithfulScheme E.group (Multiplicative (ZMod n)) :=
  cyclicDistinctParameter E.group (H.generatorCurveMarking hP)
    (H.generatorCurveMarking_distinct hP (hP.universallyDistinct H))

/-- The cyclic parameter evaluates to the original generator powers in the smooth group. -/
@[reassoc] theorem retainedEtaleCyclicParameter_value (j : Multiplicative (ZMod n)) :
    retainedEtaleCyclicParameter H hP ≫ faithfulInclusion E.group _ ≫
      value E.group _ j = H.generatorCurveMarking hP j :=
  cyclicDistinctParameter_value E.group (H.generatorCurveMarking hP)
    (H.generatorCurveMarking_distinct hP (hP.universallyDistinct H)) j

variable (b : Bool) (q : S ⟶ normalizedLocus n b)
  (a : CompatibleIso ((normalizedSubgroup n b).baseChange q) H)
  (m : Labels (normalizedAuxiliaryOrder b) →* (𝟙_ (Over S) ⟶ E.group))
  (hm : ∀ i, pullSection q (normalizedAuxiliaryMarking n b i) ≫ a.curve.hom.group = m i)
  (hc : Nat.Coprime (normalizedAuxiliaryOrder b) n)

/-- The independent original auxiliary and cyclic frames as a faithful full parameter. -/
def retainedFullParameter : 𝟙_ (Over S) ⟶
    faithfulScheme E.group (Labels (normalizedAuxiliaryOrder b) × Multiplicative (ZMod n)) :=
  coprimeParameter E.group _ _ (normalizedAuxiliaryLabels_pow b)
    (fun j ↦ congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero n j.toAdd))
    hc (retainedAuxiliaryParameter H b q a m hm) (retainedEtaleCyclicParameter H hP)

/-- Full evaluation is the product of the two unchanged original marked sections. -/
@[reassoc] theorem retainedFullParameter_value
    (i : Labels (normalizedAuxiliaryOrder b)) (j : Multiplicative (ZMod n)) :
    retainedFullParameter H hP b q a m hm hc ≫ faithfulInclusion E.group _ ≫
      value E.group _ (i, j) = m i * H.generatorCurveMarking hP j := by
  rw [retainedFullParameter, coprimeParameter_value, coprimeMarking_apply]
  change ((_ ≫ faithfulInclusion E.group _) ≫ value E.group _ i) *
    ((_ ≫ faithfulInclusion E.group _) ≫ value E.group _ j) = _
  rw [Category.assoc, Category.assoc,
    retainedAuxiliaryParameter_value, retainedEtaleCyclicParameter_value]

/-- Restriction to the auxiliary factor retains every original auxiliary section. -/
@[reassoc] theorem retainedFullParameter_auxiliary (i : Labels (normalizedAuxiliaryOrder b)) :
    retainedFullParameter H hP b q a m hm hc ≫ faithfulInclusion E.group _ ≫
      value E.group _ (i, 1) = m i := by
  rw [retainedFullParameter_value, map_one, _root_.mul_one]

/-- Restriction to the cyclic factor retains every original Cartier generator power. -/
@[reassoc] theorem retainedFullParameter_cyclic (j : Multiplicative (ZMod n)) :
    retainedFullParameter H hP b q a m hm hc ≫ faithfulInclusion E.group _ ≫
      value E.group _ (1, j) = H.generatorCurveMarking hP j := by
  rw [retainedFullParameter_value, map_one, _root_.one_mul]

end FLT.Mazur.CyclicCharacteristicAtlas
