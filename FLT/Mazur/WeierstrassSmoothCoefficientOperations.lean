/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientNegation
public import FLT.Mazur.WeierstrassSmoothCoefficientCartesian
public import FLT.Mazur.WeierstrassSmoothNegation

/-!
# Coefficient comparison preserves the smooth zero and inverse

The comparisons use the actual original smooth open and global cubic
operations. No condition on the discriminant or coefficient algebra is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The original smooth coefficient map preserves the actual zero section. -/
@[reassoc] theorem originalSmoothCoefficientMap_zero :
    integralSmoothZero V ≫ originalSmoothCoefficientMap S W = q ≫ integralSmoothZero W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, originalSmoothCoefficientMap_inclusion,
    integralSmoothZero_inclusion_assoc, integralSmoothZero_inclusion,
    integralCoefficientMorphism_zero]

/-- The original smooth coefficient map commutes with the actual inverse. -/
@[reassoc] theorem originalSmoothCoefficientMap_negation :
    integralSmoothNegation V ≫ originalSmoothCoefficientMap S W =
      originalSmoothCoefficientMap S W ≫ integralSmoothNegation W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, originalSmoothCoefficientMap_inclusion,
    integralSmoothNegation_inclusion, integralSmoothNegation_inclusion_assoc,
    originalSmoothCoefficientMap_inclusion_assoc, integralCoefficientMorphism_negation]

end FLT.Mazur.WeierstrassDividedDepth
