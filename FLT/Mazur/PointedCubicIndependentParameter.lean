/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IndependentCyclicAuxiliaryScheme
public import FLT.Mazur.PointedCubicCoefficientParameter
public import FLT.Mazur.PointedCubicCyclicAuxiliaryCover

/-!
# Original cubic parameters without a coprimality hypothesis

Project the auxiliary and cyclic markings separately through the same original
coefficient comparison. Their pair defines a universal independent parameter
on the actual etale auxiliary cover, including for even cyclic orders.
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

/-- The same original cubic group is separated under its coefficient bundling. -/
local instance : IsSeparated (pointedCubicCoefficientGroup W).X.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- The original cyclic marking over the actual auxiliary cover and exact universal coefficients. -/
def pointedCubicIndependentCyclicParameter :
    (Over.map (pointedCubicCoefficientBase W h₂)).obj (pointedCubicAuxiliaryCover W h₂) ⟶
      faithfulScheme universalGroup (Multiplicative (ZMod n)) :=
  pointedCubicFullCoefficientParameter W h₂ (Multiplicative (ZMod n))
    (pointedCubicAuxiliaryBaseTest W h₂ ≫
      cyclicDistinctParameter (pointedCubicCoefficientGroup W).X φ hφ)

/-- Both independent faithful markings on the actual original etale cover. -/
def pointedCubicIndependentParameter :
    (Over.map (pointedCubicCoefficientBase W h₂)).obj (pointedCubicAuxiliaryCover W h₂) ⟶
      independentCyclicAuxiliaryScheme n :=
  independentCyclicLift n
    (pointedCubicFullCoefficientParameter W h₂ (Labels 4) (pointedCubicAuxiliaryParameter W h₂))
    (pointedCubicIndependentCyclicParameter W h₂ φ hφ)

/-- The independent parameter retains exactly the original coefficient map. -/
@[reassoc] theorem pointedCubicIndependentParameter_base :
    (pointedCubicIndependentParameter W h₂ φ hφ).left ≫
      (independentCyclicAuxiliaryScheme n).hom =
        (pointedCubicAuxiliaryCover W h₂).hom ≫ pointedCubicCoefficientBase W h₂ :=
  (pointedCubicIndependentParameter W h₂ φ hφ).w

/-- Every cyclic label is unchanged through the original coefficient group comparison. -/
theorem pointedCubicIndependentParameter_cyclic (b : Multiplicative (ZMod n)) :
    (pointedCubicIndependentParameter W h₂ φ hφ ≫ independentCyclicParameter n ≫
      faithfulInclusion universalGroup (Multiplicative (ZMod n)) ≫
        value universalGroup (Multiplicative (ZMod n)) b).left =
      (pointedCubicAuxiliaryCover W h₂).hom ≫ (φ b).left ≫
        (pointedCubicCoefficientGroupIso W h₂).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (pointedCubicCoefficientBase W h₂) := by
  rw [← Category.assoc, ← Category.assoc,
    show pointedCubicIndependentParameter W h₂ φ hφ ≫ independentCyclicParameter n =
      pointedCubicIndependentCyclicParameter W h₂ φ hφ from
        independentCyclicLift_cyclic n _ _]
  rw [Category.assoc]
  change (pointedCubicFullCoefficientParameter W h₂ (Multiplicative (ZMod n)) _ ≫
    faithfulInclusion _ _ ≫ value _ _ b).left = _
  rw [pointedCubicFullCoefficientParameter_value, Category.assoc,
    cyclicDistinctParameter_value, Over.comp_left, Category.assoc]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
