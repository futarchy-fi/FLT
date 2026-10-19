/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The cyclic geometric kernel of an exact torsion quotient

An exact line inclusion identifies the Vélu kernel with the standard cyclic
group. This uses exactness, not a cardinality assertion about all n-torsion.
-/

@[expose] public noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) (n : ℕ)
variable (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n)
variable (i : ZMod n →ₗ[ZMod n] (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n)
variable (hi : Function.Injective i) (hex : LinearMap.range i = LinearMap.ker q)

/-- An exact line inclusion parametrizes the geometric kernel, preserving addition. -/
def torsionKernelEquivOfExact : ZMod n ≃+ torsionKernel E n q := by
  have hqi (x : ZMod n) : q (i x) = 0 := by
    change i x ∈ LinearMap.ker q
    rw [← hex]
    exact ⟨x, rfl⟩
  let f : ZMod n →+ torsionKernel E n q := {
    toFun := fun x ↦ ⟨(i x).val, i x, hqi x, rfl⟩
    map_zero' := by
      apply Subtype.ext
      change (i 0).val = 0
      exact congrArg (fun t ↦ t.val) (map_zero i)
    map_add' := by
      intro x y
      apply Subtype.ext
      change (i (x + y)).val = (i x).val + (i y).val
      exact congrArg (fun t ↦ t.val) (map_add i x y) }
  apply AddEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply hi
    apply Subtype.ext
    exact congrArg (fun t : torsionKernel E n q ↦ t.val) hxy
  · rintro ⟨P, t, ht, rfl⟩
    have ht' : t ∈ LinearMap.range i := by
      rw [hex]
      exact ht
    obtain ⟨x, hx⟩ := ht'
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (i x).val = t.val
    exact congrArg (fun t ↦ t.val) hx

/-- The kernel parametrization is the original inclusion on geometric points. -/
theorem torsionKernelEquivOfExact_apply (x : ZMod n) :
    (torsionKernelEquivOfExact E n q i hi hex x).val = (i x).val := rfl

include i hi hex in
/-- The geometric kernel of an exact standard line has precisely n points. -/
theorem torsionKernel_card_of_exact : Nat.card (torsionKernel E n q) = n := by
  rw [← Nat.card_congr (torsionKernelEquivOfExact E n q i hi hex).toEquiv]
  exact Nat.card_zmod n

include i hi hex in
/-- The geometric kernel of an exact standard line is cyclic. -/
theorem torsionKernel_isAddCyclic_of_exact : IsAddCyclic (torsionKernel E n q) :=
  (torsionKernelEquivOfExact E n q i hi hex).isAddCyclic.mp inferInstance

include hi in
/-- The image of one under the original line inclusion has exact order n. -/
theorem torsionKernel_generator_order : addOrderOf (i 1).val = n := by
  let f : ZMod n →+ (E⁄(AlgebraicClosure ℚ)).Point := {
    toFun := fun x ↦ (i x).val
    map_zero' := congrArg (fun t ↦ t.val) (map_zero i)
    map_add' := fun x y ↦ congrArg (fun t ↦ t.val) (map_add i x y) }
  have hf : Function.Injective f := fun x y h ↦ hi (Subtype.ext h)
  exact (addOrderOf_injective f hf 1).trans (ZMod.addOrderOf_one n)

end WeierstrassCurve.Velu
