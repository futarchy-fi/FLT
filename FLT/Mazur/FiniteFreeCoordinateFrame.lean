/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Constructing a complete frame from separated coordinates of matching rank

The Chinese remainder theorem gives surjectivity of coordinate evaluation.
A basis with the same index set makes this map an endomorphism of a finite
free module. Surjectivity then gives injectivity over arbitrary commutative
rings, including nonreduced rings. No decomposition is supplied as input.
-/

@[expose] public noncomputable section
open Module
namespace FLT.Mazur.FiniteFreeCoordinateFrame
variable {T A I : Type*} [CommRing T] [CommRing A] [Algebra T A] [Finite I]
  (l : I → A →ₐ[T] T)

/-- Simultaneous evaluation along the actual scalar-compatible coordinates. -/
def evaluation : A →ₐ[T] (I → T) := AlgHom.pi l

/-- Pairwise comaximal coordinate kernels make simultaneous evaluation surjective. -/
theorem evaluation_surjective
    (hl : Pairwise fun i j ↦
      IsCoprime (RingHom.ker (l i).toRingHom) (RingHom.ker (l j).toRingHom)) :
    Function.Surjective (evaluation l) := by
  let _ := Fintype.ofFinite I
  intro x
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal hl (fun i ↦ algebraMap T A (x i))
  refine ⟨a, funext fun i ↦ ?_⟩
  have h := ha i
  change l i (a - algebraMap T A (x i)) = 0 at h
  rw [map_sub, (l i).commutes] at h
  exact sub_eq_zero.mp h

/-- A basis of the coordinate rank turns surjective evaluation into a bijection. -/
theorem evaluation_bijective (b : Basis I T A)
    (hl : Pairwise fun i j ↦
      IsCoprime (RingHom.ker (l i).toRingHom) (RingHom.ker (l j).toRingHom)) :
    Function.Bijective (evaluation l) := by
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  have hs := evaluation_surjective l hl
  let f : Module.End T A := b.equivFun.symm.toLinearMap.comp (evaluation l).toLinearMap
  have hf : Function.Surjective f := b.equivFun.symm.surjective.comp hs
  have hi := Module.End.injective_of_surjective T A hf
  exact ⟨fun _ _ h ↦ hi (congrArg b.equivFun.symm h), hs⟩

/-- The full product frame is constructed from coordinate separation and a matching basis. -/
def frame (b : Basis I T A)
    (hl : Pairwise fun i j ↦
      IsCoprime (RingHom.ker (l i).toRingHom) (RingHom.ker (l j).toRingHom)) :
    A ≃ₐ[T] (I → T) := AlgEquiv.ofBijective (evaluation l) (evaluation_bijective l b hl)

/-- The constructed complete frame keeps each supplied coordinate. -/
theorem frame_apply (b : Basis I T A)
    (hl : Pairwise fun i j ↦
      IsCoprime (RingHom.ker (l i).toRingHom) (RingHom.ker (l j).toRingHom))
    (a : A) (i : I) : frame l b hl a i = l i a := rfl

end FLT.Mazur.FiniteFreeCoordinateFrame
