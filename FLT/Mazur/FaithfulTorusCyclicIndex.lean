/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TorusPointUnitEquiv
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# A faithful finite cyclic torus labeling has invertible index

The actual label generator gives a primitive root in the coefficient field.
Its order is prime to the characteristic, so its index is also a unit in the
original power-series coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.FaithfulTorusCyclicIndex
universe u
variable (K : Type u) [Field K] (n : ℕ)
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)

/-- The coefficient of every original torus label, as a multiplicative field element. -/
def coefficient : Multiplicative (ZMod n) →* K :=
  (Units.coeHom K).comp ((TorusPointUnitEquiv.equivalence K).symm.toMonoidHom.comp labels)

include hlabels in
/-- The original faithful label generator is a primitive root of the specified order. -/
theorem generator_primitive :
    IsPrimitiveRoot (coefficient K n labels (Multiplicative.ofAdd (1 : ZMod n))) n := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have h : Function.Injective (coefficient K n labels) :=
    Units.val_injective.comp ((TorusPointUnitEquiv.equivalence K).symm.injective.comp hlabels)
  rw [orderOf_injective (coefficient K n labels) h, orderOf_ofAdd_eq_addOrderOf,
    ZMod.addOrderOf_one]

variable [NeZero n]

include hlabels in
/-- Faithful finite cyclic torus labels force their index to be a unit in the field. -/
theorem index_unit : IsUnit (n : K) := by
  let _ := (generator_primitive K n labels hlabels).neZero'
  exact isUnit_iff_ne_zero.mpr (NeZero.ne (n : K))

include hlabels in
/-- The same index is a unit in the original complete power-series base. -/
theorem powerSeries_index_unit : IsUnit (n : PowerSeries K) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simpa only [map_natCast] using index_unit K n labels hlabels

end FLT.Mazur.FaithfulTorusCyclicIndex
