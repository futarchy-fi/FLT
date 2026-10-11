/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Quasi-finiteness along a cartesian identity

If a morphism restricts to the identity on a cartesian test scheme, every
point fiber through that test scheme is a singleton. Finite type then gives
quasi-finiteness at each of these points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartesianIdentity
universe u
variable {T X Y : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ Y)
  (h : IsPullback (𝟙 T) i (i ≫ f) f)

include h

/-- A cartesian identity retains the entire point fiber, not just its test points. -/
theorem preimage_singleton (t : T) : f ⁻¹' {f (i t)} = {i t} := by
  ext x
  constructor
  · intro hx
    have he : (i ≫ f) t = f x := hx.symm
    obtain ⟨z, hz, hzx⟩ := Scheme.exists_preimage_of_isPullback h t x he
    have hzt : z = t := hz
    simpa only [hzt, Set.mem_singleton_iff] using hzx.symm
  · rintro rfl
    rfl

/-- Finite type and a cartesian identity give quasi-finiteness on the test image. -/
theorem quasiFiniteAt [LocallyOfFiniteType f] (t : T) : f.QuasiFiniteAt (i t) := by
  have hf : (f ⁻¹' {f (i t)}).Finite := by
    rw [preimage_singleton i f h t]
    exact Set.finite_singleton _
  have : Finite (f.fiber (f (i t))) := (f.fiberHomeo _).finite_iff.mpr hf
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

end FLT.Mazur.CartesianIdentity
