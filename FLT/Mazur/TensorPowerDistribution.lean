/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerReassociation

/-!
# Distribution of powers over the sheaf tensor

Associativity and symmetry give the actual sheaf isomorphism between the
product of powers and the power of the product, including the zeroth power.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

open ModuleSheafTensor ModuleSheafTensorAssociator

variable {X : Scheme.{u}}

/-- Interchange the middle factors of two tensor products. -/
def tensorMiddleExchangeIso (A B C D : X.Modules) :
    tensor (tensor A B) (tensor C D) ≅ tensor (tensor A C) (tensor B D) :=
  associator A B (tensor C D) ≪≫
    congr (Iso.refl A) (associator B C D).symm ≪≫
    congr (Iso.refl A) (congr (comm B C) (Iso.refl D)) ≪≫
    congr (Iso.refl A) (associator C B D) ≪≫
    (associator A C (tensor B D)).symm

/-- Products of equally indexed tensor powers identify with powers of the product. -/
def tensorPowerDistributionIso (M N : X.Modules) : ∀ n : ℕ,
    tensor (tensorPower M n) (tensorPower N n) ≅ tensorPower (tensor M N) n
  | 0 => leftUnitor (structureModule X)
  | n + 1 => tensorMiddleExchangeIso M (tensorPower M n) N (tensorPower N n) ≪≫
      congr (Iso.refl _) (tensorPowerDistributionIso M N n)

end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
