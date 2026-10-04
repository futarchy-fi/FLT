/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SemilinearFixedAlgebra

/-!
# Tensor actions for general coefficient twists

Tensoring a coefficient action with an integral algebra action gives a genuine
semilinear group action, including its cocycle law. The twist coordinates are
the fixed subalgebra. No Hopf structure is presumed on these coordinates.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent

universe u
variable {R S H : Type u} {G : Type*} [CommRing R] [CommRing S] [CommRing H]
  [Algebra R S] [Algebra R H] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))

/-- The simultaneous action on coefficient and group-scheme coordinates. -/
def twistAction : G →* (S ⊗[R] H ≃ₐ[R] S ⊗[R] H) where
  toFun g := Algebra.TensorProduct.congr (σ g) (τ g)
  map_one' := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s h =>
      change σ 1 s ⊗ₜ[R] τ 1 h = s ⊗ₜ[R] h
      simp
  map_mul' g h := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s x =>
      change σ (g * h) s ⊗ₜ[R] τ (g * h) x = σ g (σ h s) ⊗ₜ[R] τ g (τ h x)
      simp only [map_mul]
      rfl

/-- The action on pure tensors has the prescribed two factors. -/
theorem twistAction_tmul (g : G) (s : S) (x : H) :
    twistAction σ τ g (s ⊗ₜ[R] x) = σ g s ⊗ₜ[R] τ g x := rfl

/-- Tensor twisting respects the coefficient action, so scalar recovery applies. -/
theorem twistAction_coefficients (g : G) (s : S) :
    twistAction σ τ g (algebraMap S (S ⊗[R] H) s) =
      algebraMap S (S ⊗[R] H) (σ g s) := by
  change σ g s ⊗ₜ[R] τ g 1 = σ g s ⊗ₜ[R] 1
  rw [map_one]

/-- The integral coordinate algebra of the simultaneous twist. -/
abbrev twistModel := fixed (twistAction σ τ)

/-- Finite flat coefficients and coordinates give finite flat twist coordinates. -/
theorem twistModel_finiteFlat [IsDedekindDomain R]
    [Module.Finite R S] [Module.Flat R S] [Module.Finite R H] [Module.Flat R H] :
    HopfAlgebra.IsFiniteFlat R (twistModel σ τ) :=
  fixed_finiteFlat (twistAction σ τ)

/-- Over a local Dedekind base these twist coordinates are free. -/
theorem twistModel_free [IsDedekindDomain R] [IsLocalRing R]
    [Module.Finite R S] [Module.Flat R S] [Module.Finite R H] [Module.Flat R H] :
    Module.Free R (twistModel σ τ) :=
  fixed_free (twistAction σ τ)

end SemilinearDescent
