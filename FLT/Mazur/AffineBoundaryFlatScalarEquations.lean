/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryScalarObstructionGeometry

/-!
# Branch scalar equations descend to original denominators

On a flat scalar branch, the denominator may be a function of that branch,
not the image of an original scalar. Actual power equations on the full
Cartesian coefficient pullback produce an original scalar denominator.
No branch finiteness, affine branch, or global surjectivity is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
  {Y : Scheme} (g : Y ⟶ Spec (.of T)) [Flat g] [LocallyOfFinitePresentation g]
local notation "π" => boundaryScalarProjection s κ
local notation "Z" => (pullback π g : Scheme)
local notation "p" => pullback.fst π g
local notation "q" => pullback.snd π g

/-- A branch function killing every full test power gives a whole original scalar neighborhood. -/
theorem boundaryScalar_mem_of_flat_equations (y : Y) (x : Γ(Y, ⊤))
    (hx : y ∈ Y.basicOpen x)
    (he : ∀ t ∈ a, ∃ k : ℕ,
      ((p).appTop (boundaryCoordinate s κ t)) ^ k * (q).appTop x = 0) :
    g y ∈ boundaryScalarNilpotenceOpen s κ a := by
  apply boundaryScalar_mem_of_flat_neighborhood s κ a g (Y.basicOpen x) y hx
  intro z hz t ht
  obtain ⟨k, hk⟩ := he t ht
  let Q : PrimeSpectrum Γ(Z, ⊤) := (Z).toSpecΓ z
  have hqx : (q).appTop x ∉ Q.asIdeal := by
    change z ∈ (Z).toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen ((q).appTop x)
    rw [Scheme.toSpecΓ_preimage_basicOpen, ← Scheme.preimage_basicOpen_top]
    exact hz
  have hqt : (p).appTop (boundaryCoordinate s κ t) ∈ Q.asIdeal := by
    apply Q.isPrime.mem_of_pow_mem k
    apply (Q.isPrime.mem_or_mem (hk ▸ Q.asIdeal.zero_mem)).resolve_right hqx
  by_contra ht'
  have hmem : (p).appTop (boundaryCoordinate s κ t) ∉ Q.asIdeal := by
    change z ∈ (Z).toSpecΓ ⁻¹ᵁ
      PrimeSpectrum.basicOpen ((p).appTop (boundaryCoordinate s κ t))
    rw [Scheme.toSpecΓ_preimage_basicOpen, ← Scheme.preimage_basicOpen_top,
      boundaryCoordinate_basicOpen]
    exact ht'
  exact hmem hqt

/-- The descended denominator is an original scalar, even for a new branch function. -/
theorem boundaryScalar_denominator_of_flat_equations (y : Y) (x : Γ(Y, ⊤))
    (hx : y ∈ Y.basicOpen x)
    (he : ∀ t ∈ a, ∃ k : ℕ,
      ((p).appTop (boundaryCoordinate s κ t)) ^ k * (q).appTop x = 0) :
    ∃ (order : ℕ) (r : T), r ∉ (g y).asIdeal ∧
      boundaryScalarHom s κ r ∈ ((boundaryTestIdeal s κ a) ^ order).annihilator :=
  (mem_boundaryScalarNilpotenceOpen s κ a (g y)).mp
    (boundaryScalar_mem_of_flat_equations s κ a g y x hx he)

/-- The whole actual test-kernel product avoids the original prime reached by the branch. -/
theorem boundaryTestKernel_avoids_of_flat_equations (y : Y) (x : Γ(Y, ⊤))
    (hx : y ∈ Y.basicOpen x)
    (he : ∀ t ∈ a, ∃ k : ℕ,
      ((p).appTop (boundaryCoordinate s κ t)) ^ k * (q).appTop x = 0) :
    ¬ boundaryTestKernelProduct s κ a ≤ (g y).asIdeal :=
  (boundaryScalar_mem_iff_testKernelProduct s κ a (g y)).mp
    (boundaryScalar_mem_of_flat_equations s κ a g y x hx he)

end FLT.Mazur.AffineScalarBoundaryNilpotence
