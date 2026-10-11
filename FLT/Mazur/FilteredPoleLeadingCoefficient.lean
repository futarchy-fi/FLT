/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredPoleBasis

/-!
# Nonzero top coefficients in a filtered basis

If all but the last basis vector lie in a lower filtration piece, a vector
outside that piece has nonzero last coordinate. This keeps the actual
basis expansion and will detect the cubic's leading coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FilteredPoleBasis
open Module
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (P : ℕ → Submodule k V)

/-- A basis expansion in a pole space is also the original ambient vector expansion. -/
theorem sum_repr_coe {N D : ℕ} (b : Basis (Fin N) k (P D)) (z : P D) :
    ∑ i, b.repr z i • (b i : V) = (z : V) := by
  simpa only [map_sum, map_smul, Submodule.subtype_apply] using
    congrArg (P D).subtype (b.sum_repr z)

/-- A section outside the lower pole space has nonzero last coordinate. -/
theorem last_repr_ne_zero {N D E : ℕ} (b : Basis (Fin (N + 1)) k (P D))
    (hb : ∀ i : Fin N, (b i.castSucc : V) ∈ P E)
    (z : P D) (hz : (z : V) ∉ P E) : b.repr z (Fin.last N) ≠ 0 := by
  intro he
  apply hz
  have hs := sum_repr_coe P b z
  rw [Fin.sum_univ_castSucc, he, zero_smul, add_zero] at hs
  rw [← hs]
  exact (P E).sum_mem (fun i _ ↦ (P E).smul_mem _ (hb i))

end FLT.Mazur.FilteredPoleBasis
