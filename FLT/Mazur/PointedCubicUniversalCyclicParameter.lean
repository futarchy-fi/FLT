/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicCoefficientParameter
public import FLT.Mazur.PointedCubicCyclicAuxiliaryCover

/-!
# Actual universal full parameters retaining original cubic cyclic sections

The original pointed cubic's etale auxiliary cover maps to the universal full
marking scheme. This map retains all five original coefficients and every
original cyclic section through the established group comparison.
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

/-- The original pointed cubic group remains separated. -/
local instance : IsSeparated (pointedCubicFamily W).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- The bundled coefficient group is the same separated original carrier. -/
local instance : IsSeparated (pointedCubicCoefficientGroup W).X.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- The actual full universal parameter on the original cubic's etale auxiliary cover. -/
def pointedCubicUniversalCyclicParameter :
    (Over.map (pointedCubicCoefficientBase W h₂)).obj (pointedCubicAuxiliaryCover W h₂) ⟶
      cyclicAuxiliaryScheme n :=
  pointedCubicFullCoefficientParameter W h₂ (CyclicLabels n)
    (pointedCubicCyclicParameter W h₂ φ hφ h)

/-- The full universal parameter retains exactly the original coefficient base map. -/
@[reassoc] theorem pointedCubicUniversalCyclicParameter_base :
    (pointedCubicUniversalCyclicParameter W h₂ φ hφ h).left ≫ (cyclicAuxiliaryScheme n).hom =
      (pointedCubicAuxiliaryCover W h₂).hom ≫ pointedCubicCoefficientBase W h₂ :=
  (pointedCubicUniversalCyclicParameter W h₂ φ hφ h).w

/-- Each universal cyclic label is the original section through the actual coefficient map. -/
theorem pointedCubicUniversalCyclicParameter_cyclic (b : Multiplicative (ZMod n)) :
    (pointedCubicUniversalCyclicParameter W h₂ φ hφ h ≫ cyclicAuxiliaryInclusion n ≫
      value universalGroup (CyclicLabels n) (1, b)).left =
        (pointedCubicAuxiliaryCover W h₂).hom ≫ (φ b).left ≫
          (pointedCubicCoefficientGroupIso W h₂).hom.hom.hom.hom.left ≫
            pullback.fst universalGroup.hom (pointedCubicCoefficientBase W h₂) := by
  change (pointedCubicFullCoefficientParameter W h₂ (CyclicLabels n)
    (pointedCubicCyclicParameter W h₂ φ hφ h) ≫ faithfulInclusion _ _ ≫ value _ _ (1, b)).left = _
  rw [pointedCubicFullCoefficientParameter_value]
  change (pointedCubicCyclicParameter W h₂ φ hφ h ≫
    faithfulInclusion (pointedCubicFamily W).group (CyclicLabels n) ≫
      value (pointedCubicFamily W).group (CyclicLabels n) (1, b)).left ≫ _ = _
  rw [pointedCubicCyclicParameter_cyclic, Over.comp_left, Category.assoc]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
