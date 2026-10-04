/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat

/-!
# Fixed algebras for finite semilinear descent

The action is given by algebra automorphisms over the base, and need not fix
an intermediate coefficient ring. Orbit sums land in the actual fixed algebra.
Over a Dedekind base, finite torsion-free ambient coordinates give finite flat
fixed coordinates; over a local base these coordinates are free.
-/

@[expose] public noncomputable section
open scoped BigOperators TensorProduct
namespace SemilinearDescent

universe u
variable {R B : Type u} {G : Type*} [CommRing R] [CommRing B] [Algebra R B] [Group G]
  (ρ : G →* (B ≃ₐ[R] B))

/-- The subalgebra fixed by every element of the descent group. -/
def fixed : Subalgebra R B where
  carrier := {x | ∀ g, ρ g x = x}
  mul_mem' hx hy g := by rw [map_mul, hx, hy]
  add_mem' hx hy g := by rw [map_add, hx, hy]
  algebraMap_mem' r g := (ρ g).commutes r

/-- Equivariant maps restrict to the actual fixed subalgebras. -/
def fixedMap {C : Type u} [CommRing C] [Algebra R C]
    (τ : G →* (C ≃ₐ[R] C)) (f : B →ₐ[R] C)
    (hf : ∀ g x, τ g (f x) = f (ρ g x)) : fixed ρ →ₐ[R] fixed τ :=
  (f.domRestrict (fixed ρ)).codRestrict (fixed τ) (fun x g ↦ by
    change τ g (f x) = f x
    rw [hf, x.property])

variable [Fintype G]

/-- Summing an orbit gives an invariant, without dividing by the group order. -/
def orbitSum : B →ₗ[R] fixed ρ where
  toFun x := ⟨∑ g, ρ g x, fun h ↦ by
    simp only [map_sum]
    have hm (g : G) : ρ h (ρ g x) = ρ (h * g) x := by rw [map_mul]; rfl
    simp only [hm]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ ↦ rfl)⟩
  map_add' x y := Subtype.ext (by simp [Finset.sum_add_distrib])
  map_smul' r x := Subtype.ext (by simp [Finset.smul_sum])

/-- Orbit summation may be moved past an invariant factor. -/
theorem orbitSum_mul_fixed (s : B) (x : fixed ρ) :
    (orbitSum ρ (s * x) : B) = (∑ g, ρ g s) * x := by
  change (∑ g, ρ g (s * x)) = _
  have hx (g : G) : ρ g (x : B) = x := x.property g
  simp only [map_mul, hx, Finset.sum_mul]

omit [Fintype G] in
/-- Fixed coordinates are finite flat over a Dedekind base. -/
theorem fixed_finiteFlat [IsDedekindDomain R] [Module.Finite R B]
    [Module.IsTorsionFree R B] : HopfAlgebra.IsFiniteFlat R (fixed ρ) := by
  let : Module.Finite R (fixed ρ) := Module.Finite.of_injective
    (fixed ρ).val.toLinearMap Subtype.val_injective
  let : Module.IsTorsionFree R (fixed ρ) := Function.Injective.moduleIsTorsionFree
    (fixed ρ).val Subtype.val_injective (fun r x ↦ (fixed ρ).val.toLinearMap.map_smul r x)
  exact ⟨⟩

omit [Fintype G] in
/-- Over a local Dedekind base the fixed coordinates are finite free. -/
theorem fixed_free [IsDedekindDomain R] [IsLocalRing R] [Module.Finite R B]
    [Module.IsTorsionFree R B] : Module.Free R (fixed ρ) := by
  let := fixed_finiteFlat ρ
  exact Module.free_of_flat_of_isLocalRing

end SemilinearDescent
