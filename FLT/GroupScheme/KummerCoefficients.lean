/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.CocycleFiniteGalois
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import FLT.Mathlib.FieldTheory.Galois.Infinite

/-!
# Discrete roots of unity as Galois coefficients

The additive notation is for use with the explicit continuous cocycle API.
The action is the natural field action, with no chosen primitive root.
-/

@[expose] public section

namespace KummerTheory

variable (L : Type*) [Field L] (n : ℕ)

/-- Roots of unity, written additively and given the discrete topology. -/
def RootModule := Additive (rootsOfUnity n L)

instance : AddCommGroup (RootModule L n) := inferInstanceAs (AddCommGroup (Additive _))
instance : TopologicalSpace (RootModule L n) := ⊥
instance : DiscreteTopology (RootModule L n) := ⟨rfl⟩
instance [NeZero n] : Finite (RootModule L n) := inferInstanceAs (Finite (Additive _))

variable {L n}

/-- Forget a root coefficient to a field unit. -/
def rootUnit (x : RootModule L n) : Lˣ := x.toMul.1

/-- Root coefficients embed in the field. -/
theorem rootUnit_injective : Function.Injective (rootUnit (L := L) (n := n)) :=
  fun _ _ h ↦ Subtype.ext h

@[simp] theorem rootUnit_zero : rootUnit (0 : RootModule L n) = 1 := rfl
@[simp] theorem rootUnit_add (x y : RootModule L n) :
    rootUnit (x + y) = rootUnit x * rootUnit y := rfl
@[simp] theorem rootUnit_sub (x y : RootModule L n) :
    rootUnit (x - y) = rootUnit x / rootUnit y := rfl

/-- The defining power relation. -/
theorem rootUnit_pow (x : RootModule L n) : rootUnit x ^ n = 1 := x.toMul.2

variable {K : Type*} [Field K] [Algebra K L]

instance rootAction : DistribMulAction Gal(L/K) (RootModule L n) where
  smul g x := Additive.ofMul (restrictRootsOfUnity g n x.toMul)
  one_smul x := by apply rootUnit_injective; apply Units.ext; rfl
  mul_smul g h x := by apply rootUnit_injective; apply Units.ext; rfl
  smul_zero g := by apply rootUnit_injective; apply Units.ext; exact map_one g
  smul_add g x y := by apply rootUnit_injective; apply Units.ext; exact map_mul g _ _

/-- The coefficient action is the natural action on field units. -/
@[simp] theorem rootUnit_smul (g : Gal(L/K)) (x : RootModule L n) :
    rootUnit (g • x) = g • rootUnit x := rfl

/-- Evaluation fibers are open in the Krull topology, so all root orbits are continuous. -/
theorem continuous_root_orbit [Algebra.IsAlgebraic K L] (x : RootModule L n) :
    Continuous (fun g : Gal(L/K) ↦ g • x) := by
  apply IsLocallyConstant.continuous
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro y
  have heq : {g : Gal(L/K) | g • x = y} =
      {g : Gal(L/K) | g (rootUnit x : L) = (rootUnit y : L)} := by
    ext g
    exact ⟨fun h ↦ congrArg (fun z : RootModule L n ↦ (rootUnit z : L)) h,
      fun h ↦ rootUnit_injective (Units.ext h)⟩
  change IsOpen {g : Gal(L/K) | g • x = y}
  rw [heq]
  exact ContinuousSMulDiscrete.isOpen_smul_eq Gal(L/K) _ _

end KummerTheory
