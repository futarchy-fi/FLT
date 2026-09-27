/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Slop.Ribet_Lemma.Brauer_Nesbitt
public import Mathlib.LinearAlgebra.Determinant

/-! # A trivial quotient determines the subcharacter

In dimension two, the kernel of an invariant surjective functional is a stable
line. Its character is the determinant, since the quotient action is trivial.
-/

@[expose] public section

namespace StableLattice

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A two-dimensional representation with determinant `χ` and a trivial
one-dimensional quotient is an extension of the trivial character by `χ`. -/
theorem isExtensionOf_det_one_of_trivial_quotient
    (ρ : Representation k G V) (hdim : Module.finrank k V = 2)
    (χ : G →* kˣ) (hdet : ∀ g, LinearMap.det (ρ g) = (χ g : k))
    (π : V →ₗ[k] k) (hs : Function.Surjective π)
    (hπ : ∀ g v, π (ρ g v) = π v) :
    IsExtensionOf ρ χ 1 := by
  have : FiniteDimensional k V := Module.finite_of_finrank_pos (by omega)
  have hker : Module.finrank k (LinearMap.ker π) = 1 := by
    have hrank := π.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
      hdim] at hrank
    omega
  have hstable (g : G) : LinearMap.ker π ≤ (LinearMap.ker π).comap (ρ g) := by
    intro v hv
    change π (ρ g v) = 0
    rw [hπ]
    exact hv
  obtain ⟨φ, hφ⟩ := exists_character_of_stable_line ρ hker (fun g => by
    rintro _ ⟨v, hv, rfl⟩
    exact hstable g hv)
  have hchar (g : G) : (φ g : k) = (χ g : k) := by
    have hres : (ρ g).restrict (hstable g) =
        (φ g : k) • (LinearMap.id : LinearMap.ker π →ₗ[k] LinearMap.ker π) := by
      ext v
      exact hφ g v v.property
    have hquot : (LinearMap.ker π).mapQ (LinearMap.ker π) (ρ g) (hstable g) =
        LinearMap.id := by
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v =>
        simpa [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub] using
          sub_eq_zero.mpr (hπ g v)
    have hd := (ρ g).det_eq_det_mul_det (LinearMap.ker π) (hstable g)
    rw [hdet, hres, hquot, LinearMap.det_smul, hker, pow_one,
      LinearMap.det_id, LinearMap.det_id, mul_one, mul_one] at hd
    exact hd.symm
  refine ⟨LinearMap.ker π, hker, ?_, ?_⟩
  · intro g v hv
    rw [hφ g v hv, hchar]
  · intro g v
    simp [LinearMap.mem_ker, map_sub, hπ]

end StableLattice
