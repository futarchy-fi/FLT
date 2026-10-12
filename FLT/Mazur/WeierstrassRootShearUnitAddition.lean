/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeSmoothPointAddition
public import FLT.Mazur.WeierstrassRootShearSmoothParameter
public import FLT.Mazur.WeierstrassSplitNodalUnitAddition

/-!
# The actual root-sheared smooth law multiplies Laurent units

The original smooth addition is compatible with the proper root shear.
Consequently its ordered tangent parameters multiply over every algebra,
including nonreduced algebras, on the original singular cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (r : R) (a : Rˣ)
  (ha : (a : R) = W.a₁ + 2 * r) (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
  (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "U" => splitNodalEquation a
local notation "C" => (VariableChange.mk 1 0 r 0 : VariableChange R)
local notation "he" => rootShearCurve_eq_splitNodal W r a ha hr h3 h4 h6
local notation "I" => rootShearTorusSmoothIso W r a ha hr h3 h4 h6
local notation "e" => integralVariableChangeSmoothMap W U C he

/-- A Laurent unit gives the actual smooth input on the original root-split cubic. -/
def rootShearSmoothUnitInput (p : Aˣ) : Over.mk s ⟶ Over.mk (integralSmoothStructure W) :=
  laurentUnitOverPoint p ≫ (rootShearTorusSmoothOverIso W r a ha hr h3 h4 h6).hom

/-- The actual input uses precisely the original geometric parameter comparison. -/
theorem rootShearSmoothUnitInput_parameter (p : Aˣ) :
    (rootShearSmoothUnitInput W r a ha hr h3 h4 h6 p).left =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) p).toRingHom) ≫
        (I).hom := rfl

/-- The original input is the split input followed by the full proper smooth shear. -/
theorem rootShearSmoothUnitInput_split (p : Aˣ) :
    (rootShearSmoothUnitInput W r a ha hr h3 h4 h6 p).left =
      (splitNodalSmoothUnitInput a p).left ≫ e := (Category.assoc _ _ _).symm

/-- The independent smooth sum multiplies the original root-shifted tangent units. -/
theorem rootShearSmoothUnitInput_addition (p q : Aˣ) :
    smoothPairPointAddition W
        (rootShearSmoothUnitInput W r a ha hr h3 h4 h6 p).left
        (rootShearSmoothUnitInput W r a ha hr h3 h4 h6 q).left
        ((rootShearSmoothUnitInput W r a ha hr h3 h4 h6 p).w.trans
          (rootShearSmoothUnitInput W r a ha hr h3 h4 h6 q).w.symm) =
      (rootShearSmoothUnitInput W r a ha hr h3 h4 h6 (p * q)).left := by
  let hpair := (splitNodalSmoothUnitInput a p).w.trans (splitNodalSmoothUnitInput a q).w.symm
  have hs : smoothPairPointAddition U (splitNodalSmoothUnitInput a p).left
      (splitNodalSmoothUnitInput a q).left hpair = (splitNodalSmoothUnitInput a (p * q)).left :=
    splitNodalSmoothUnitInput_addition a p q
  have ht := integralVariableChangeSmoothMap_pointAddition W U C he
    (splitNodalSmoothUnitInput a p).left (splitNodalSmoothUnitInput a q).left hpair
  rw [hs] at ht
  simpa only [rootShearSmoothUnitInput_split] using ht.symm

end FLT.Mazur.WeierstrassIntegralChart
