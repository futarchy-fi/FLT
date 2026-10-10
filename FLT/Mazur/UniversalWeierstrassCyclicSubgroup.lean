/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicAuxiliary
public import FLT.Mazur.RelativeMarkingSections
public import FLT.Mazur.RelativeCyclicSubgroup

/-!
# The actual cyclic subgroup over the auxiliary parameter scheme

The universal faithful marking constructs a closed finite etale subgroup of
rank p in the pulled-back universal cubic. Its marked generator is a Cartier
generator, and its ideal is the product of the original section-orbit ideals.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.UniversalWeierstrass

open AuxiliaryLevel

variable (p : ℕ) [NeZero p]

/-- The original universal cubic pulled back to the auxiliary marking scheme. -/
def cyclicFamily : GeneralizedEllipticCurve (cyclicAuxiliaryScheme p).left :=
  universalCurve.baseChange (cyclicAuxiliaryScheme p).hom

/-- The cyclic factor of the original marking as actual sections of this family. -/
def cyclicMarking : Multiplicative (ZMod p) →*
    (𝟙_ (Over (cyclicAuxiliaryScheme p).left) ⟶ (cyclicFamily p).group) :=
  ((RelativeMarkingSections.sectionHom (cyclicAuxiliaryScheme p) universalGroup).comp
    (markingOf universalGroup (CyclicLabels p) (cyclicAuxiliaryInclusion p))).comp
      (MonoidHom.inr _ _)

/-- The cyclic marking remains distinct on every nonempty test scheme. -/
theorem cyclicMarking_distinct : UniversallyDistinctSections.UniversallyDistinct
    (fun i : ZMod p ↦ cyclicMarking p (Multiplicative.ofAdd i)) := by
  change UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod p ↦
    RelativeMarkingSections.asSection (cyclicAuxiliaryScheme p)
      (markingOf universalGroup (CyclicLabels p) (cyclicAuxiliaryInclusion p)
        (1, Multiplicative.ofAdd i)))
  apply RelativeMarkingSections.universallyDistinct
  intro V g hV i j hij
  let _ := hV
  have hh := faithful_marking_injective universalGroup (CyclicLabels p) g
  have he : markingOf universalGroup (CyclicLabels p) (g ≫ cyclicAuxiliaryInclusion p)
      (1, Multiplicative.ofAdd i) =
      markingOf universalGroup (CyclicLabels p) (g ≫ cyclicAuxiliaryInclusion p)
        (1, Multiplicative.ofAdd j) := by
    simpa only [markingOf_comp] using hij
  exact congrArg (fun a : CyclicLabels p ↦ a.2.toAdd) (hh he)

/-- The universal marking's actual closed subgroup of rank p. -/
def cyclicSubgroup : (cyclicFamily p).FiniteSubgroup p :=
  (cyclicFamily p).relativeCyclicSubgroup (cyclicMarking p) (cyclicMarking_distinct p)

/-- The constructed finite subgroup is etale over the parameter scheme. -/
theorem cyclicSubgroup_etale : Etale (cyclicSubgroup p).carrier.hom :=
  (cyclicFamily p).relativeCyclicSubgroup_etale (cyclicMarking p) (cyclicMarking_distinct p)

/-- Its generator is a section of the actual subgroup, rather than an abstract label. -/
def cyclicSubgroupGenerator :
    𝟙_ (Over (cyclicAuxiliaryScheme p).left) ⟶ (cyclicSubgroup p).carrier :=
  (cyclicFamily p).relativeCyclicGenerator (cyclicMarking p) (cyclicMarking_distinct p)

/-- Projection of the included generator recovers the original universal cyclic section. -/
@[reassoc] theorem cyclicSubgroupGenerator_original :
    (cyclicSubgroupGenerator p ≫ (cyclicSubgroup p).inclusion).left ≫
      pullback.fst universalGroup.hom (cyclicAuxiliaryScheme p).hom =
        (cyclicSection p (𝟙 _)).left := by
  change ((cyclicFamily p).relativeCyclicGenerator (cyclicMarking p)
    (cyclicMarking_distinct p) ≫ ((cyclicFamily p).relativeCyclicSubgroup
      (cyclicMarking p) (cyclicMarking_distinct p)).inclusion).left ≫ _ = _
  rw [GeneralizedEllipticCurve.relativeCyclicGenerator_inclusion]
  change (RelativeMarkingSections.asSection (cyclicAuxiliaryScheme p)
    (markingOf universalGroup (CyclicLabels p) (cyclicAuxiliaryInclusion p)
      (cyclicLabel p))).left ≫ _ = _
  rw [RelativeMarkingSections.section_fst]
  simp only [cyclicSection, Category.id_comp]

/-- The pulled-back cubic is a smooth relative curve. -/
instance cyclicFamily_smooth : SmoothOfRelativeDimension 1 (cyclicFamily p).curve.hom := by
  let _ := WeierstrassIntegralChart.integralCurveStructure_smooth_dimension
    smoothEquation smoothEquation_discriminant
  change SmoothOfRelativeDimension 1
    (pullback.snd (WeierstrassIntegralChart.integralCurveStructure smoothEquation)
      (cyclicAuxiliaryScheme p).hom)
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The actual universal section satisfies the Cartier generator condition. -/
theorem cyclicSubgroupGenerator_isCartierGenerator :
    (cyclicSubgroup p).IsCartierGenerator (cyclicSubgroupGenerator p) :=
  (cyclicFamily p).relativeCyclicGenerator_isCartierGenerator
    (cyclicMarking p) (cyclicMarking_distinct p)

/-- The universal subgroup is cyclic in the existing moduli interface. -/
theorem cyclicSubgroup_isCyclic : (cyclicSubgroup p).IsCyclic :=
  (cyclicSubgroupGenerator_isCartierGenerator p).isCyclic _

/-- Its original kernel is a relative effective Cartier divisor of the cubic family. -/
theorem cyclicSubgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier (cyclicFamily p).curve.hom (cyclicSubgroup p).ideal :=
  (cyclicSubgroupGenerator_isCartierGenerator p).2.1

end FLT.Mazur.UniversalWeierstrass
