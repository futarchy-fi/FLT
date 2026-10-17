/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionTensorCoordinates
public import FLT.Mazur.BoundaryCorrectionFlatDescent

/-!
# Descending actual flat ambient coefficient equations

Input consists of actual coefficients in the extended chart modules, satisfying
the exact boundary and all mixed equations together. Finite product comparison
assembles them into the full tensor kernel. Flatness then gives finitely many
original solution families and a nonvanishing original scalar when applicable.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  (S : Type*) [CommRing S] [Algebra R S]
  (s : S) (z : ∀ i, S ⊗[R] A i)
  (hb : ∀ i, (φ i).toLinearMap.lTensor S (z i) = 0)
  (he : ∀ i j, (p i j).toLinearMap.lTensor S (z i) -
    (q i j).toLinearMap.lTensor S (z j) = s ⊗ₜ[R] (p i j (u i) - q i j (u j)))

include hb he in
/-- All separately extended equations assemble into one original tensor kernel solution. -/
theorem ambientCorrection_mem_kernel :
    (correctionSystem φ p q u).lTensor S
      ((tensorCorrectionCoordinates (A := A) S).symm (s, z)) = 0 := by
  rw [tensorCorrectionSystem_eq_zero_iff, LinearEquiv.apply_symm_apply]
  exact ⟨hb, he⟩

omit [Fintype ι]
variable [Finite ι] [Module.Flat R S]

include hb he in
/-- A finite family of original shared corrections reconstructs every actual ambient solution. -/
theorem ambientCorrection_finite_original :
    ∃ (n : ℕ) (a : Fin n → S) (y : Fin n → correctionSolutions φ p q u),
      s = ∑ k, algebraMap R S (y k).val.1 * a k ∧
      ∀ i, z i = ∑ k, a k ⊗ₜ[R] (y k).val.2 i := by
  let _ := Fintype.ofFinite ι
  obtain ⟨n, a, y, hy⟩ := flatCorrection_exists_finite φ p q u S
    ((tensorCorrectionCoordinates (A := A) S).symm (s, z))
    (ambientCorrection_mem_kernel φ p q u S s z hb he)
  have hc := congrArg (tensorCorrectionCoordinates (A := A) S) hy
  rw [LinearEquiv.apply_symm_apply, map_sum] at hc
  simp only [tensorCorrectionCoordinates_tmul] at hc
  refine ⟨n, a, y, ?_, fun i ↦ ?_⟩
  · simpa only [Prod.fst_sum] using congrArg Prod.fst hc
  · simpa only [Prod.snd_sum, Finset.sum_apply] using congrArg (fun w ↦ w.2 i) hc

include hb he in
/-- A nonvanishing ambient multiplier yields an actual original nonvanishing solution pair. -/
theorem ambientCorrection_original_nonvanishing (P : Ideal S) (hs : s ∉ P) :
    ∃ y : correctionSolutions φ p q u, algebraMap R S y.val.1 ∉ P := by
  let _ := Fintype.ofFinite ι
  apply flatCorrection_exists_nonvanishing_solution φ p q u S P
    ((tensorCorrectionCoordinates (A := A) S).symm (s, z))
    (ambientCorrection_mem_kernel φ p q u S s z hb he)
  rw [← tensorCorrectionCoordinates_fst, LinearEquiv.apply_symm_apply]
  exact hs

end FLT.Mazur.BoundaryCorrectionIdeal
