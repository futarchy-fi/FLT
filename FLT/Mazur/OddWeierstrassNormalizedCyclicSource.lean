/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedCyclicValue
public import FLT.Mazur.OddWeierstrassCyclicHomSourceDivisor
public import FLT.Mazur.OddWeierstrassNormalizationCurve
public import FLT.Mazur.GroupSchemeBaseChangeProjections

/-!
# The full source of an actual normalized odd cyclic parameter

The universal coefficient pullback is the original normalized proper group.
Every cyclic section retains its inverse-normalization formula.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel WeierstrassIntegralChart GeneralizedEllipticCurve
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {n : ℕ} [NeZero n]
  (p : (Over.map (auxiliaryCoefficientBase g)).obj (𝟙_ (Over (Spec (.of R)))) ⟶ levelThree)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over (Spec (.of R))) ⟶ (auxiliaryPullbackGroup g).X))
local notation "f" => Over.Hom.left (auxiliaryNormalizedCyclicParameter g p φ)
local notation "G" => integralCurveGroup oddChartEquation oddChart_discriminant
local notation "b" => cyclicHomAuxiliaryPoint n f ≫ levelThree.hom

/-- Reconstructing the cyclic source retains exactly the normalized coefficient map. -/
theorem auxiliaryNormalizedCyclicSource_base : auxiliaryNormalizedCoefficientBase g = b := by
  rw [cyclicHomAuxiliaryPoint, Category.assoc, (cyclicHomAuxiliary n).w]
  exact ((auxiliaryNormalizedCyclicParameter g p φ).w.trans (Category.id_comp _)).symm

/-- The reconstructed source is the whole normalized proper group. -/
irreducible_def auxiliaryNormalizedCyclicSourceGroupIso :
    auxiliaryNormalizedGroup g ≅ (Over.pullback b).mapCommGrp.obj G :=
  auxiliaryNormalizedCoefficientGroupIso g ≪≫
    GroupSchemeBaseChange.congrIso (auxiliaryNormalizedCyclicSource_base g p φ) G

/-- Its universal projection is the actual normalized coefficient comparison. -/
@[reassoc] theorem auxiliaryNormalizedCyclicSourceGroupIso_fst :
    (auxiliaryNormalizedCyclicSourceGroupIso g p φ).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom b =
        (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (auxiliaryNormalizedCoefficientBase g) := by
  rw [auxiliaryNormalizedCyclicSourceGroupIso_def]
  change (_ ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z ↦ (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left ≫ z)
      (GroupSchemeBaseChange.congrIso_hom_fst
        (auxiliaryNormalizedCyclicSource_base g p φ) G))

/-- Every cyclic section of the source is the transported original section. -/
theorem auxiliaryNormalizedCyclicSourceGroupIso_marking (i : Multiplicative (ZMod n)) :
    auxiliaryNormalizedCyclicMarking g φ i ≫
      (auxiliaryNormalizedCyclicSourceGroupIso g p φ).hom.hom.hom.hom =
        cyclicHomSourceMarking n f i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (auxiliaryNormalizedCyclicMarking g φ i ≫
      (auxiliaryNormalizedCyclicSourceGroupIso g p φ).hom.hom.hom.hom).left ≫
        pullback.fst universalGroup.hom b =
      (cyclicHomSourceMarking n f i).left ≫ pullback.fst universalGroup.hom b
    rw [Over.comp_left, Category.assoc, auxiliaryNormalizedCyclicSourceGroupIso_fst,
      cyclicHomSourceMarking_fst]
    exact (auxiliaryNormalizedCyclicParameter_value g φ p i).symm
  · exact Over.w _ |>.trans (Over.w _).symm

/-- The normalized parameter retains the whole curve, its action and its zero section. -/
irreducible_def auxiliaryNormalizedCyclicSourceCurveIso :
    auxiliaryNormalizedCurve g ≅ cyclicHomSourceCurve n f := by
  let e : (auxiliaryNormalizedCurve g).group ≅ (cyclicHomSourceCurve n f).group :=
    (CommGrp.forget _).mapIso (auxiliaryNormalizedCyclicSourceGroupIso g p φ)
  let _ : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (auxiliaryNormalizedCyclicSourceGroupIso g p φ).hom.hom.hom.hom)
  let _ := SmoothOfRelativeDimension.smooth 1 (cyclicHomSourceCurve n f).curve.hom
  exact isoOfSmoothGroup _ _ e

/-- The full curve comparison keeps every normalized cyclic section. -/
theorem auxiliaryNormalizedCyclicSourceCurveIso_marking (i : Multiplicative (ZMod n)) :
    auxiliaryNormalizedCyclicMarking g φ i ≫
      (auxiliaryNormalizedCyclicSourceCurveIso g p φ).hom.group =
        cyclicHomSourceMarking n f i := by
  rw [auxiliaryNormalizedCyclicSourceCurveIso_def]
  exact auxiliaryNormalizedCyclicSourceGroupIso_marking g p φ i

end FLT.Mazur.OddWeierstrassParameter
