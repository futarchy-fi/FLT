/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicModuliBridge

/-!
# The modular bridge retains the original universal Cartier subgroup

At the identity parameter the source construction is compatibly isomorphic to
the original universal cyclic level. Naturality then identifies the bridge on
every source with pullback of that same original level.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n]

/-- The universal source construction retains the original universal coefficient map. -/
theorem cyclicUniversalSource_base :
    cyclicSchemeAuxiliaryPoint n (𝟙 _) ≫ levelFour.hom = (cyclicAuxiliaryScheme n).hom := by
  change (𝟙 _ ≫ (forgetCyclic n).left) ≫ levelFour.hom = _
  rw [Category.id_comp, (forgetCyclic n).w]

/-- The original source group at the identity is the original universal cyclic group. -/
irreducible_def cyclicUniversalSourceGroupIso :
    auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n (𝟙 _)) ≅
      CommGrp.mk (cyclicFamily n).group :=
  GroupSchemeBaseChange.congrIso (cyclicUniversalSource_base n)
    (WeierstrassIntegralChart.integralCurveGroup smoothEquation smoothEquation_discriminant)

/-- The universal comparison retains the exact original projection. -/
@[reassoc] theorem cyclicUniversalSourceGroupIso_fst :
    (cyclicUniversalSourceGroupIso n).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (cyclicAuxiliaryScheme n).hom =
        pullback.fst universalGroup.hom
          (cyclicSchemeAuxiliaryPoint n (𝟙 _) ≫ levelFour.hom) := by
  rw [cyclicUniversalSourceGroupIso_def]
  exact GroupSchemeBaseChange.congrIso_hom_fst (cyclicUniversalSource_base n) _

/-- The original universal source comparison extends to the full generalized curves. -/
def cyclicUniversalSourceCurveIso : cyclicSourceCurve n (𝟙 _) ≅ cyclicFamily n := by
  let _ := SmoothOfRelativeDimension.smooth 1 (cyclicFamily n).curve.hom
  let e : (cyclicSourceCurve n (𝟙 _)).group ≅ (cyclicFamily n).group :=
    (CommGrp.forget _).mapIso (cyclicUniversalSourceGroupIso n)
  let _ : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (cyclicUniversalSourceGroupIso n).hom.hom.hom.hom)
  exact isoOfSmoothGroup _ _ e

/-- The actual cyclic sections agree with the original universal sections. -/
theorem cyclicUniversalSourceCurveIso_marking (i : Multiplicative (ZMod n)) :
    cyclicSourceMarking n (𝟙 _) i ≫ (cyclicUniversalSourceCurveIso n).hom.group =
      cyclicMarking n i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((cyclicSchemeOriginalMarking n (𝟙 _) (1, i)).left ≫
      (cyclicUniversalSourceGroupIso n).hom.hom.hom.hom.left) ≫ _ = _
    rw [Category.assoc, cyclicUniversalSourceGroupIso_fst,
      cyclicSchemeOriginalMarking_fst, Category.id_comp]
    exact (RelativeMarkingSections.section_fst (cyclicAuxiliaryScheme n) _).symm
  · exact (Over.w _).trans (Over.w _).symm

/-- The source construction retains the original universal Cartier subgroup, compatibly. -/
def cyclicUniversalSourceCompatibleIso :
    CompatibleIso (cyclicSourceSubgroup n (𝟙 _)) (cyclicSubgroup n) :=
  relativeCyclicSubgroupCompatibleIso (cyclicSourceMarking n (𝟙 _)) (cyclicMarking n)
    (cyclicSourceMarking_distinct n (𝟙 _)) (cyclicMarking_distinct n)
    (cyclicUniversalSourceCurveIso n) (cyclicUniversalSourceCurveIso_marking n)

/-- The modular bridge on the identity point is the original universal ample cyclic class. -/
theorem cyclicSourceModuliClass_id :
    cyclicSourceModuliClass n (𝟙 _) = cyclicModuliClass n :=
  Quotient.sound ⟨cyclicUniversalSourceCompatibleIso n⟩

/-- On every source, the bridge is actual pullback of the original ample cyclic level. -/
theorem cyclicSourceModuliClass_original {T : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    cyclicSourceModuliClass n f = ampleCyclicClassesPullback f n (cyclicModuliClass n) := by
  have h := cyclicSourceModuliClass_pullback n (𝟙 _) f
  rw [Category.comp_id, cyclicSourceModuliClass_id] at h
  exact h

/-- Every represented slice point pulls back the original universal cyclic level. -/
theorem cyclicNormalizedSliceModuliMap_original {T : Scheme}
    (f : T ⟶ cyclicNormalizedSlice n) :
    (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up f) =
      ampleCyclicClassesPullback (f ≫ cyclicNormalizedSliceInclusion n) n
        (cyclicModuliClass n) :=
  cyclicSourceModuliClass_original n (f ≫ cyclicNormalizedSliceInclusion n)

/-- The represented slice carries the restriction of the original universal cyclic level. -/
theorem cyclicNormalizedSliceModuliClass_original :
    cyclicNormalizedSliceModuliClass n =
      ampleCyclicClassesPullback (cyclicNormalizedSliceInclusion n) n (cyclicModuliClass n) := by
  have h := cyclicNormalizedSliceModuliMap_original n (𝟙 _)
  rw [Category.id_comp] at h
  exact h

end FLT.Mazur.UniversalWeierstrass
