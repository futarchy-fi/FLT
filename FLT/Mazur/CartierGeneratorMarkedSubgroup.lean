/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorSplitPresentation
public import FLT.Mazur.RelativeCyclicSubgroupComparison

/-!
# Recovering the original subgroup from its marked curve sections

The generator induces a cyclic marking in the original smooth group. Its
constructed subgroup is compatibly isomorphic to the original subgroup, with
the entire curve, inclusion and specified generator retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversallyDistinctSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier}
  (hP : H.IsCartierGenerator P)

/-- The generator powers marked in the original smooth curve group. -/
def generatorCurveMarking : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group) where
  toFun i := H.generatorPowers P hP.1 i ≫ H.inclusion
  map_one' := by rw [map_one, MonObj.one_comp]
  map_mul' i j := by rw [map_mul, MonObj.mul_comp]

variable (hd : UniversallyDistinct (fun i : ZMod n ↦
  H.generatorPowers P hP.1 (Multiplicative.ofAdd i)))

include hd in
/-- The original subgroup inclusion preserves universal distinctness of the marking. -/
theorem generatorCurveMarking_distinct : UniversallyDistinct (fun i : ZMod n ↦
    H.generatorCurveMarking hP (Multiplicative.ofAdd i)) := by
  intro V g hV i j hij
  have : Mono H.inclusion := Over.mono_of_mono_left H.inclusion
  apply hd V g hV
  apply (cancel_mono H.inclusion).mp
  change g ≫ (H.generatorPowers P hP.1 (Multiplicative.ofAdd i) ≫ H.inclusion) =
    g ≫ (H.generatorPowers P hP.1 (Multiplicative.ofAdd j) ≫ H.inclusion) at hij
  simpa only [Category.assoc] using hij

/-- The constructed subgroup inclusion is the original inclusion after the cyclic map. -/
theorem generatorCurveMarking_inclusion :
    (E.relativeCyclicSubgroup (H.generatorCurveMarking hP)
      (H.generatorCurveMarking_distinct hP hd)).inclusion =
        H.generatorCyclicMap P hP.1 ≫ H.inclusion := by
  apply Sigma.hom_ext
  intro i
  change ConstantCyclicGroup.component S n i ≫
    ConstantCyclicSectionMap.toScheme (H.generatorCurveMarking hP) =
      ConstantCyclicGroup.component S n i ≫ (H.generatorCyclicMap P hP.1 ≫ H.inclusion)
  rw [ConstantCyclicSectionMap.component_toScheme, generatorCyclicMap,
    ConstantCyclicSectionMap.component_toScheme_assoc]
  rfl

/-- The marked subgroup reconstructs the original full curve and its actual subgroup. -/
def generatorMarkedCompatibleIso :
    CompatibleIso (E.relativeCyclicSubgroup (H.generatorCurveMarking hP)
      (H.generatorCurveMarking_distinct hP hd)) H where
  curve := Iso.refl E
  subgroup := H.generatorSplitIso hP hd
  isMonHom := inferInstanceAs (IsMonHom (H.generatorSplitIso hP hd).hom)
  compatible := by
    change (_ ≫ E.inclusion) ≫ 𝟙 E.curve =
      H.generatorCyclicMap P hP.1 ≫ (H.inclusion ≫ E.inclusion)
    rw [Category.comp_id, H.generatorCurveMarking_inclusion hP hd, Category.assoc]

/-- The reconstructed presentation retains the original Cartier generator itself. -/
theorem generatorMarkedCompatibleIso_generator :
    E.relativeCyclicGenerator (H.generatorCurveMarking hP)
      (H.generatorCurveMarking_distinct hP hd) ≫
        (H.generatorMarkedCompatibleIso hP hd).subgroup.hom = P := by
  dsimp only [generatorMarkedCompatibleIso, relativeCyclicGenerator]
  simpa only [Nat.cast_one, pow_one] using H.generatorSplitIso_component hP hd 1

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
