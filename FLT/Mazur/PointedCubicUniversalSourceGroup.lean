/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicUniversalCyclicParameter
public import FLT.Mazur.UniversalWeierstrassCyclicSourceMarking

/-!
# The original pointed cubic group equals its constructed full source family

The parameter's exact coefficient equation identifies the universal source
group with the pullback of the original pointed cubic group to its auxiliary
cover. The comparison retains the actual projection through the original group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
  (hφ : UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  (h : Nat.Coprime 4 n)
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicUniversalCyclicParameter W h₂ φ hφ h)
local notation "c" => pointedCubicCoefficientBase W h₂
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant

/-- The source reconstruction uses precisely the original coefficient composite. -/
theorem pointedCubicUniversalSource_base :
    k ≫ c = cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom := by
  rw [cyclicSchemeAuxiliaryPoint, Category.assoc, (forgetCyclic n).w]
  exact (pointedCubicUniversalCyclicParameter_base W h₂ φ hφ h).symm

/-- The source group is the actual base change of the original pointed cubic group. -/
irreducible_def pointedCubicUniversalSourceGroupIso :
    (Over.pullback k).mapCommGrp.obj (pointedCubicCoefficientGroup W) ≅
      auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) :=
  (Over.pullback k).mapCommGrp.mapIso (pointedCubicCoefficientGroupIso W h₂) ≪≫
    (GroupSchemeBaseChange.compIso k c G).symm ≪≫
      GroupSchemeBaseChange.congrIso (pointedCubicUniversalSource_base W h₂ φ hφ h) G

/-- Projection of the source comparison retains the two actual original group maps. -/
@[reassoc] theorem pointedCubicUniversalSourceGroupIso_fst :
    (pointedCubicUniversalSourceGroupIso W h₂ φ hφ h).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom) =
        pullback.fst (pointedCubicCoefficientGroup W).X.hom k ≫
          (pointedCubicCoefficientGroupIso W h₂).hom.hom.hom.hom.left ≫
            pullback.fst universalGroup.hom c := by
  rw [pointedCubicUniversalSourceGroupIso_def]
  let a := ((Over.pullback k).mapCommGrp.map
    (pointedCubicCoefficientGroupIso W h₂).hom).hom.hom.hom.left
  let b := (GroupSchemeBaseChange.compIso k c G).inv.hom.hom.hom.left
  let d := (GroupSchemeBaseChange.congrIso
    (pointedCubicUniversalSource_base W h₂ φ hφ h) G).hom.hom.hom.hom.left
  let p := pullback.fst (G).X.hom (cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom)
  change (a ≫ b ≫ d) ≫ p = _
  calc
    _ = a ≫ b ≫ (d ≫ p) := by simp only [Category.assoc]
    _ = a ≫ b ≫ pullback.fst (G).X.hom (k ≫ c) :=
      congrArg (fun z ↦ a ≫ b ≫ z)
        (GroupSchemeBaseChange.congrIso_hom_fst
          (pointedCubicUniversalSource_base W h₂ φ hφ h) G)
    _ = a ≫ pullback.fst ((Over.pullback c).obj (G).X).hom k ≫
        pullback.fst (G).X.hom c :=
      congrArg (fun z ↦ a ≫ z) (GroupSchemeBaseChange.compIso_inv_fst k c G)
    _ = (a ≫ pullback.fst ((Over.pullback c).obj (G).X).hom k) ≫
        pullback.fst (G).X.hom c := (Category.assoc _ _ _).symm
    _ = _ := (congrArg (fun z ↦ z ≫ pullback.fst (G).X.hom c)
      (GroupSchemeBaseChange.map_hom_fst k (pointedCubicCoefficientGroupIso W h₂).hom)).trans
        (Category.assoc _ _ _)

end FLT.Mazur.GeneralizedEllipticCurve
