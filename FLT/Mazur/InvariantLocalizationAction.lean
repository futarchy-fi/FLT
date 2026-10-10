/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupInvariantRing
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The action on an invariant principal localization

Localizing at a fixed function extends the original action canonically. The
extension is constructed from the localization universal property, including
its multiplication and identity laws.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A]
  (r : invariantRing G A)

/-- Extend a group element to the localization at a fixed function. -/
def localizedActionHom (g : G) : Localization.Away (r : A) →+* Localization.Away (r : A) :=
  IsLocalization.Away.lift (r : A)
    (g := (algebraMap A (Localization.Away (r : A))).comp
      (MulSemiringAction.toRingHom G A g)) (by
        change IsUnit (algebraMap A (Localization.Away (r : A)) (g • (r : A)))
        rw [r.property g]
        exact IsLocalization.Away.algebraMap_isUnit (r : A))

/-- The extension agrees with the original action on every numerator. -/
@[simp]
theorem localizedActionHom_algebraMap (g : G) (a : A) :
    localizedActionHom G A r g (algebraMap A (Localization.Away (r : A)) a) =
      algebraMap A (Localization.Away (r : A)) (g • a) :=
  IsLocalization.Away.lift_eq _ _ _

/-- Localization of the action respects the identity. -/
theorem localizedActionHom_one : localizedActionHom G A r 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (r : A))
  ext a
  simp only [RingHom.comp_apply, localizedActionHom_algebraMap, one_smul, RingHom.id_apply]

/-- Localization of the action respects multiplication of group elements. -/
theorem localizedActionHom_mul (g h : G) :
    localizedActionHom G A r (g * h) =
      (localizedActionHom G A r g).comp (localizedActionHom G A r h) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (r : A))
  ext a
  simp only [RingHom.comp_apply, localizedActionHom_algebraMap, mul_smul]

/-- The canonical action on the principal localization. -/
@[instance_reducible]
def localizedAction : MulSemiringAction G (Localization.Away (r : A)) :=
  MulSemiringAction.compHom _
    ({ toFun := localizedActionHom G A r
       map_one' := localizedActionHom_one G A r
       map_mul' := localizedActionHom_mul G A r } :
      G →* (Localization.Away (r : A) →+* Localization.Away (r : A)))

/-- The canonical localization homomorphism is equivariant for the constructed action. -/
theorem localizedAction_smul (g : G) (a : A) :
    let _ := localizedAction G A r
    g • algebraMap A (Localization.Away (r : A)) a =
      algebraMap A (Localization.Away (r : A)) (g • a) :=
  localizedActionHom_algebraMap G A r g a

end FLT.Mazur.FiniteGroupQuotient
