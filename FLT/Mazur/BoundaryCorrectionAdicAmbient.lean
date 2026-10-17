/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionFlatDescent
public import FLT.Mazur.FiniteErrorTensorPairs

/-!
# Constructing and descending corrections from finite ambient adic errors

All approximate errors are measured in the full boundary and independent mixed
equation module over a flat algebra of the original scalars. One finite error
module, valid at every order, suffices to construct an exact ambient solution
and then a nonvanishing original shared correction family.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
open FiniteErrorLinearLifting
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  (S : Type*) [CommRing S] [Algebra R S]

/-- An assembled ambient correction pair has exactly the specified multiplier. -/
theorem tensorPair_correctionMultiplier (s : S) (z : S ⊗[R] (∀ i, A i)) :
    tensorCorrectionMultiplier (A := A) S (tensorPair S (s, z)) = s := by
  change (TensorProduct.rid R S) ((LinearMap.fst R R (∀ i, A i)).baseChange S
    (tensorPair S (s, z))) = s
  rw [tensorPair_fst, TensorProduct.rid_tmul, one_smul]

variable [IsNoetherianRing S]
  (J : Ideal S) (E : Submodule S (S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)))
  (hE : E.FG)
  (h : ∀ n : ℕ, ∃ z : S ⊗[R] (∀ i, A i),
    (correctionSystem φ p q u).baseChange S (tensorPair S (1, z)) ∈ J ^ n • E)
include hE h

/-- Finite ambient errors construct an exact correction retaining every original equation. -/
theorem adicAmbientCorrection_exists (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ x : S ⊗[R] (R × ∀ i, A i),
      (correctionSystem φ p q u).lTensor S x = 0 ∧
      tensorCorrectionMultiplier (A := A) S x ∉ P := by
  obtain ⟨s, z, hs, hz⟩ :=
    exists_tensor_pair_nonvanishing S (correctionSystem φ p q u) J E hE h P hJP hP
  exact ⟨tensorPair S (s, z), hz, by rwa [tensorPair_correctionMultiplier]⟩

variable [Module.Flat R S]

/-- The constructed flat ambient correction descends to an actual original solution family. -/
theorem adicAmbientCorrection_original (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ y : correctionSolutions φ p q u, algebraMap R S y.val.1 ∉ P := by
  obtain ⟨x, hx, hs⟩ := adicAmbientCorrection_exists φ p q u S J E hE h P hJP hP
  exact flatCorrection_exists_nonvanishing_solution φ p q u S P x hx hs

/-- The result supplies actual compatible original numerators on every chart at once. -/
theorem adicAmbientCorrection_numerators (P : Ideal S) (hJP : J ≤ P) (hP : P ≠ ⊤) :
    ∃ (a : R) (w : ∀ i, A i), algebraMap R S a ∉ P ∧
      (∀ i, φ i (w i) = φ i (algebraMap R (A i) a) * φ i (u i)) ∧
      ∀ i j, p i j (w i) = q i j (w j) := by
  obtain ⟨y, hy⟩ := adicAmbientCorrection_original φ p q u S J E hE h P hJP hP
  obtain ⟨w, hw, hc⟩ := (mem_iff_numerators _ _ _ _ _ _ _).mp
    (correctionMultiplier_mem φ p q u y)
  exact ⟨y.val.1, w, hy, hw, hc⟩

end FLT.Mazur.BoundaryCorrectionIdeal
