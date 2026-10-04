/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicClosure
public import FLT.PadicHodgeTheory.ComplexScalarClosed

/-! # The original Galois action on the completed cyclotomic union -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Every original Galois automorphism preserves each actual cyclotomic level. -/
theorem padicCyclotomic_galois_mem (σ : PadicGalois p) (n : ℕ)
    (x : PadicAlgCl p) (hx : x ∈ padicCyclotomicTower p n) :
    σ x ∈ padicCyclotomicTower p n := by
  refine IntermediateField.adjoin_induction ℚ_[p]
    (p := fun y _ ↦ σ y ∈ padicCyclotomicTower p n) ?_ ?_ ?_ ?_ ?_ hx
  · rintro ζ ⟨k, hk, _, hζ⟩
    obtain rfl : k = p ^ n := hk
    apply padicCyclotomicTower_root_mem
    rw [← map_pow, hζ, map_one]
  · intro a; rw [σ.commutes]; exact IntermediateField.algebraMap_mem _ a
  · intro a b _ _ ha hb; rw [map_add]; exact (padicCyclotomicTower p n).add_mem ha hb
  · intro a _ ha; rw [map_inv₀]; exact (padicCyclotomicTower p n).inv_mem ha
  · intro a b _ _ ha hb; rw [map_mul]; exact (padicCyclotomicTower p n).mul_mem ha hb

/-- The original action preserves the algebraic cyclotomic union. -/
theorem padicCyclotomic_galois_union_mem (σ : PadicGalois p)
    (x : padicCyclotomicUnion p) : σ (x : PadicAlgCl p) ∈ padicCyclotomicUnion p := by
  obtain ⟨n, hn⟩ := (mem_padicCyclotomicUnion p x).mp x.property
  exact (mem_padicCyclotomicUnion p _).mpr ⟨n, padicCyclotomic_galois_mem p σ (n + 1) x hn⟩

/-- Bundle the original completed action as a continuous Q_p-linear map. -/
def complexGaloisLinear (σ : PadicGalois p) : ℂ_[p] →L[ℚ_[p]] ℂ_[p] where
  toFun := complexGalois p σ
  map_add' := map_add _
  map_smul' a x := by
    simp only [Algebra.smul_def, map_mul, complexGalois_algebraMap, RingHom.id_apply]
  cont := (complexGalois_isometry p σ).continuous

/-- Continuity extends stability of the union to stability of its actual closure. -/
theorem complexCyclotomic_galois_mem (σ : PadicGalois p) (x : complexCyclotomicClosure p) :
    complexGalois p σ (x : ℂ_[p]) ∈ complexCyclotomicClosure p := by
  apply closure_minimal ?_
    (isClosed_closure.preimage (complexGalois_isometry p σ).continuous) x.property
  rintro _ ⟨b, rfl⟩
  apply subset_closure
  refine ⟨⟨σ (b : PadicAlgCl p), padicCyclotomic_galois_union_mem p σ b⟩, ?_⟩
  exact (complexGalois_coe p σ b).symm

/-- Restrict the original action to the completed cyclotomic union. -/
def complexCyclotomicGalois (σ : PadicGalois p) :
    complexCyclotomicClosure p →L[ℚ_[p]] complexCyclotomicClosure p :=
  ((complexGaloisLinear p σ).comp (complexCyclotomicClosure p).subtypeL).codRestrict
    (complexCyclotomicClosure p) (complexCyclotomic_galois_mem p σ)

/-- The restricted action still acts by the original automorphism on C_p. -/
@[simp] theorem complexCyclotomicGalois_coe (σ : PadicGalois p)
    (x : complexCyclotomicClosure p) :
    (complexCyclotomicGalois p σ x : ℂ_[p]) = complexGalois p σ (x : ℂ_[p]) := rfl

/-- On algebraic points, restriction agrees with the original algebraic automorphism. -/
theorem complexCyclotomicGalois_inclusion (σ : PadicGalois p) (x : padicCyclotomicUnion p) :
    complexCyclotomicGalois p σ (complexCyclotomicInclusion p x) =
      complexCyclotomicInclusion p ⟨σ (x : PadicAlgCl p),
        padicCyclotomic_galois_union_mem p σ x⟩ := by
  apply Subtype.ext
  exact complexGalois_coe p σ x

end PadicHodgeTheory
