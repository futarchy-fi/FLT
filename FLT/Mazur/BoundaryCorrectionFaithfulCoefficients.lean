/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionIdeal

/-!
# Faithful coefficient tests preserve the simultaneous correction ideal

An injective ring map on each full mixed coefficient ring changes neither the
original scalar ideal nor its witnesses. The same boundary-kernel family must
solve every tested equation. Product tests may retain independent branch types
for each pair of charts.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*}
  {C E : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
  [∀ i j, CommRing (C i j)] [∀ i j, CommRing (E i j)]
  (α : ∀ i, R →+* A i) (φ : ∀ i, A i →+* B i)
  (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
  (hα : ∀ i j r, p i j (α i r) = q i j (α j r))
  (ψ : ∀ i j, C i j →+* E i j) (hψ : ∀ i j, Function.Injective (ψ i j))

include hα in
/-- Every original scalar retains its full compatibility in the tested coefficients. -/
theorem faithful_scalar_compatible (i j : ι) (r : R) :
    ((ψ i j).comp (p i j)) (α i r) = ((ψ i j).comp (q i j)) (α j r) :=
  congrArg (ψ i j) (hα i j r)

include hψ in
/-- Faithful testing keeps the very same simultaneous boundary-kernel correction witnesses. -/
theorem faithful_correction_iff (u z : ∀ i, A i) (r : R) :
    (∀ i j, p i j (z i) - q i j (z j) =
      p i j (α i r) * (p i j (u i) - q i j (u j))) ↔
    ∀ i j, ψ i j (p i j (z i)) - ψ i j (q i j (z j)) =
      ψ i j (p i j (α i r)) * (ψ i j (p i j (u i)) - ψ i j (q i j (u j))) := by
  constructor
  · intro h i j
    simpa only [map_sub, map_mul] using congrArg (ψ i j) (h i j)
  · intro h i j
    apply hψ i j
    simpa only [map_sub, map_mul] using h i j

include hψ in
/-- The tested full correction ideal is exactly the unchanged original scalar ideal. -/
theorem ideal_eq_faithful (u : ∀ i, A i) :
    ideal α φ p q hα u =
      ideal α φ (fun i j ↦ (ψ i j).comp (p i j))
        (fun i j ↦ (ψ i j).comp (q i j))
        (faithful_scalar_compatible α p q hα ψ) u := by
  ext r
  change (∃ z : ∀ i, A i, (∀ i, φ i (z i) = 0) ∧ _) ↔
    ∃ z : ∀ i, A i, (∀ i, φ i (z i) = 0) ∧ _
  apply exists_congr
  intro z
  exact and_congr_right fun _ ↦ faithful_correction_iff α p q ψ hψ u z r

end FLT.Mazur.BoundaryCorrectionIdeal
