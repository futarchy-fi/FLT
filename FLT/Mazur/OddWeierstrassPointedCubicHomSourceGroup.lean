/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassPointedCubicHomAuxiliaryParameter
public import FLT.Mazur.OddWeierstrassCyclicHomSourceDivisor
public import FLT.Mazur.GeneralizedCurveCyclicMarkingBaseChange
public import FLT.Mazur.GroupSchemeBaseChangeProjections

/-!
# Odd-chart the unrestricted cyclic source group retains the original pointed cubic

The unrestricted cyclic parameter's coefficient equation identifies the universal source
group with the pullback of the original pointed cubic group to its auxiliary
cover. The comparison retains the actual projection through the original group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve AuxiliaryLevel
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₃)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₃ φ)
local notation "c" => pointedCubicCoefficientBase W h₃
local notation "G" => integralCurveGroup oddChartEquation oddChart_discriminant

/-- The source reconstruction uses precisely the original coefficient composite. -/
theorem pointedCubicHomSource_base :
    k ≫ c = cyclicHomAuxiliaryPoint n f ≫ levelThree.hom := by
  rw [cyclicHomAuxiliaryPoint, Category.assoc, (cyclicHomAuxiliary n).w]
  exact (pointedCubicHomAuxiliaryParameter_base W h₃ φ).symm

/-- The source group is the actual base change of the original pointed cubic group. -/
irreducible_def pointedCubicHomSourceGroupIso :
    (Over.pullback k).mapCommGrp.obj (pointedCubicCoefficientGroup W) ≅
      (Over.pullback (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom)).mapCommGrp.obj G :=
  (Over.pullback k).mapCommGrp.mapIso (pointedCubicCoefficientGroupIso W h₃) ≪≫
    (GroupSchemeBaseChange.compIso k c G).symm ≪≫
      GroupSchemeBaseChange.congrIso (pointedCubicHomSource_base W h₃ φ) G

/-- Projection of the source comparison retains the two actual original group maps. -/
@[reassoc] theorem pointedCubicHomSourceGroupIso_fst :
    (pointedCubicHomSourceGroupIso W h₃ φ).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom) =
        pullback.fst (pointedCubicCoefficientGroup W).X.hom k ≫
          (pointedCubicCoefficientGroupIso W h₃).hom.hom.hom.hom.left ≫
            pullback.fst universalGroup.hom c := by
  rw [pointedCubicHomSourceGroupIso_def]
  let a := ((Over.pullback k).mapCommGrp.map
    (pointedCubicCoefficientGroupIso W h₃).hom).hom.hom.hom.left
  let b := (GroupSchemeBaseChange.compIso k c G).inv.hom.hom.hom.left
  let d := (GroupSchemeBaseChange.congrIso
    (pointedCubicHomSource_base W h₃ φ) G).hom.hom.hom.hom.left
  let p := pullback.fst (G).X.hom (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom)
  change (a ≫ b ≫ d) ≫ p = _
  calc
    _ = a ≫ b ≫ (d ≫ p) := by simp only [Category.assoc]
    _ = a ≫ b ≫ pullback.fst (G).X.hom (k ≫ c) :=
      congrArg (fun z ↦ a ≫ b ≫ z)
        (GroupSchemeBaseChange.congrIso_hom_fst
          (pointedCubicHomSource_base W h₃ φ) G)
    _ = a ≫ pullback.fst ((Over.pullback c).obj (G).X).hom k ≫
        pullback.fst (G).X.hom c :=
      congrArg (fun z ↦ a ≫ z) (GroupSchemeBaseChange.compIso_inv_fst k c G)
    _ = (a ≫ pullback.fst ((Over.pullback c).obj (G).X).hom k) ≫
        pullback.fst (G).X.hom c := (Category.assoc _ _ _).symm
    _ = _ := (congrArg (fun z ↦ z ≫ pullback.fst (G).X.hom c)
      (GroupSchemeBaseChange.map_hom_fst k (pointedCubicCoefficientGroupIso W h₃).hom)).trans
        (Category.assoc _ _ _)

/-- The actual unrestricted cyclic source comparison retains every original cyclic section. -/
theorem pointedCubicHomSourceGroupIso_cyclic (b : Multiplicative (ZMod n)) :
    pullCyclicMarking k φ b ≫
      (pointedCubicHomSourceGroupIso W h₃ φ).hom.hom.hom.hom =
        cyclicHomSourceMarking n f b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (pullCyclicMarking k φ b ≫
      (pointedCubicHomSourceGroupIso W h₃ φ).hom.hom.hom.hom).left ≫
        pullback.fst universalGroup.hom
          (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom) =
      (cyclicHomSourceMarking n f b).left ≫ pullback.fst universalGroup.hom
        (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom)
    rw [Over.comp_left, Category.assoc, pointedCubicHomSourceGroupIso_fst,
      ← Category.assoc]
    change ((pullCyclicMarking k φ b).left ≫
      pullback.fst (pointedCubicFamily W).group.hom k) ≫ _ = _
    rw [pullCyclicMarking_fst, cyclicHomSourceMarking_fst, Category.assoc]
    simpa only [Over.comp_left, Category.assoc] using
      (pointedCubicHomAuxiliaryParameter_value W h₃ φ b).symm
  · exact (pullCyclicMarking k φ b ≫
      (pointedCubicHomSourceGroupIso W h₃ φ).hom.hom.hom.hom).w.trans
        (cyclicHomSourceMarking n f b).w.symm

end FLT.Mazur.OddWeierstrassParameter
