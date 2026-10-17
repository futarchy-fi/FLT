/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomRelabelNormalization

/-!
# Extend an actual auxiliary family by the trivial cyclic marking

The extension is an actual point of the unrestricted full parameter scheme.
Its auxiliary coordinate remains the given original family on every source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ levelThree.left)

/-- Retain the actual auxiliary family and add the constant identity cyclic homomorphism. -/
def auxiliaryTrivialCyclicExtension : T ⟶ (cyclicHomAuxiliaryScheme n).left :=
  (cyclicHomLift n (Over.homMk f rfl)
    (liftMarking universalGroup (Multiplicative (ZMod n))
      (1 : Multiplicative (ZMod n) →* (Over.mk (f ≫ levelThree.hom) ⟶ universalGroup)))).left

/-- The trivial extension retains the original full auxiliary parameter exactly. -/
theorem auxiliaryTrivialCyclicExtension_auxiliary :
    cyclicHomAuxiliaryPoint n (auxiliaryTrivialCyclicExtension n f) = f :=
  congrArg Over.Hom.left (cyclicHomLift_auxiliary n _ _)

/-- Every cyclic value of the actual extension is the original identity section. -/
@[reassoc] theorem auxiliaryTrivialCyclicExtension_value (i : Multiplicative (ZMod n)) :
    auxiliaryTrivialCyclicExtension n f ≫
        (cyclicHomParameter n ≫ value universalGroup (Multiplicative (ZMod n)) i).left =
      (1 : Over.mk (f ≫ levelThree.hom) ⟶ universalGroup).left := by
  change (cyclicHomLift n _ _ ≫ cyclicHomParameter n ≫
    value universalGroup (Multiplicative (ZMod n)) i).left = _
  rw [← Category.assoc, cyclicHomLift_cyclic, liftMarking_value, MonoidHom.one_apply]

/-- Projection of full normalization recovers the actual auxiliary normalized point. -/
theorem cyclicHomNormalizedPoint_auxiliaryPoint
    (p : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    cyclicHomAuxiliaryPoint n (cyclicHomNormalizedPoint n p) =
      auxiliarySchemeNormalizedPoint (cyclicHomAuxiliaryPoint n p) :=
  cyclicHomNormalizedPoint_auxiliary n p

end FLT.Mazur.OddWeierstrassParameter
