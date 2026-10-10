/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedKernelComparison
public import FLT.Mazur.LocalizedIdealOverlapMembership

/-!
# Kernel compatibility from actual restriction paths

Localizing the target quotient constructs the comparison map on an overlap.
Equality with a second restriction path gives the denominator-power kernel
condition used in shared finite-relation patching.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizedKernelComparison

universe u v w z t

variable {P : Type u} {S : Type v} {T : Type w} {U : Type z} {V : Type t}
  [CommRing P] [CommRing S] [CommRing T] [CommRing U] [CommRing V]
  [Algebra S U] [Algebra T V]

/-- The comparison on the overlap is constructed by the localization universal property. -/
def comparison (r : S) (f : S →+* T)
    [IsLocalization.Away r U] [IsLocalization.Away (f r) V] : U →+* V :=
  IsLocalization.map V f
    ((Submonoid.map_powers f r).symm ▸ (Submonoid.powers r).le_comap_map)

/-- The constructed comparison retains the full prescribed quotient square. -/
theorem comparison_square (r : S) (f : S →+* T)
    [IsLocalization.Away r U] [IsLocalization.Away (f r) V] :
    (comparison (U := U) (V := V) r f).comp (algebraMap S U) =
      (algebraMap T V).comp f := IsLocalization.map_comp _

/-- Equality of actual restriction paths clears a killed numerator by a denominator power. -/
theorem exists_pow_mul_eq_zero_of_paths
    {S' T' : Type*} [CommRing S'] [CommRing T']
    (r x : P) (φ : P →+* S') (ψ : P →+* S)
    (f' : S' →+* T') (f : S →+* T)
    [IsLocalization.Away (ψ r) U] [IsLocalization.Away (f (ψ r)) V]
    (a : S' →+* U) (b : T' →+* V)
    (ha : a.comp φ = (algebraMap S U).comp ψ)
    (hp : (comparison (U := U) (V := V) (ψ r) f).comp a = b.comp f')
    (hx : f' (φ x) = 0) : ∃ n : ℕ, f (ψ (r ^ n * x)) = 0 := by
  exact PrincipalIdealPatching.exists_pow_mul_mem_of_overlap r x φ ψ a ha
    (RingHom.ker f') (RingHom.ker f)
    (map_ker_le_of_paths (ψ r) f _ (comparison_square (ψ r) f) f' a b hp) hx

/-- Equality of paths gives inclusion of the extended ideals, not just selected generators. -/
theorem map_ker_le_of_comparison_path
    {S' T' : Type*} [CommRing S'] [CommRing T']
    (r : S) (f : S →+* T) (f' : S' →+* T')
    [IsLocalization.Away r U] [IsLocalization.Away (f r) V]
    (a : S' →+* U) (b : T' →+* V)
    (hp : (comparison (U := U) (V := V) r f).comp a = b.comp f') :
    (RingHom.ker f').map a ≤ (RingHom.ker f).map (algebraMap S U) :=
  map_ker_le_of_paths r f _ (comparison_square r f) f' a b hp

end FLT.Mazur.LocalizedKernelComparison
