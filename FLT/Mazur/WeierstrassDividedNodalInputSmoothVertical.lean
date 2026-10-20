/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalSmoothVertical
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth

/-!
# Actual nodal depths force the full smooth input into the vertical open

The original node conditions imply every required coefficient vanishing.
Before the middle depth, relative smoothness alone therefore forces the
vertical derivative to be nonzero on the closed fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m k : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k)
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "base" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "δ" => verticalDerivative W (π ^ k) d.b3 d.b4 d.b6

include D in
/-- Full relative smoothness at a strict nodal divided point forces vertical nonvanishing. -/
theorem nodalDivided_smooth_vertical (hk : 0 < k) (hm : 2 * k < m)
    (p : PrimeSpectrum A) (hp : algebraMap R A π ∈ p.asIdeal)
    (hs : p ∈ (base).smoothLocus) : δ ∉ p.asIdeal := by
  have hmax : maximalIdeal R ≤ Ideal.comap (algebraMap R A) p.asIdeal := by
    rw [D.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact hp
  have hlin := divided_linear_deep_mem D d (by omega : k ≤ m + 1)
  have hconst := (divided_constant_exact_depth D d (by omega : 2 * k ≤ m)).1
  apply dividedNodal_smooth_vertical W (π ^ k) d.b3 d.b4 d.b6 p D.a₁_unit
    _ (hmax D.a₂_mem)
    (hmax (Ideal.pow_le_self (by omega : m + 1 - k ≠ 0) hlin.1))
    (hmax (Ideal.pow_le_self (by omega : m + 1 - k ≠ 0) hlin.2))
    (hmax (Ideal.pow_le_self (by omega : m - 2 * k ≠ 0) hconst)) hs
  rw [map_pow]
  exact p.asIdeal.pow_mem_of_mem hp k hk

variable {S : Type u} [CommRing S] [Algebra R S] (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)

include D in
/-- The actual source prime needs only relative smoothness of its supplied input. -/
theorem nodalDividedInput_smooth_vertical (hk : 0 < k) (hm : 2 * k < m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hs : Spec.map (CommRingCat.ofHom a.toRingHom) p ∈ (base).smoothLocus) :
    a δ ∉ p.asIdeal := by
  apply nodalDivided_smooth_vertical D d hk hm (PrimeSpectrum.comap a.toRingHom p) _ hs
  change a (algebraMap R A π) ∈ p.asIdeal
  simpa only [AlgHom.commutes] using hp

end FLT.Mazur.WeierstrassDividedDepth
