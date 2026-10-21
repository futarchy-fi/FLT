/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Tactic.LinearCombination

/-!
# The cokernel of full homogeneous cochain corrections

Corrections live on the whole charts. Their image consists of actual
coboundaries, not independent extensions of pairwise errors. No finiteness
of the full cokernel or vanishing of its distinguished class is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HomogeneousCochainCorrection
variable {R : Type*} [CommRing R] {ι : Type*}
  {A : ι → Type*} {B : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
  [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
  (p : ∀ i j, A i →ₐ[R] B i j) (q : ∀ i j, A j →ₐ[R] B i j)
  (I : ∀ i, Ideal (A i))

/-- All full homogeneous chart corrections, retaining every boundary ideal. -/
def cochains : Submodule R (∀ i, A i) where
  carrier := {v | ∀ i, v i ∈ I i}
  zero_mem' := fun i ↦ (I i).zero_mem
  add_mem' hu hv := fun i ↦ (I i).add_mem (hu i) (hv i)
  smul_mem' r v hv := fun i ↦ by
    change r • v i ∈ I i
    rw [Algebra.smul_def]
    exact (I i).mul_mem_left _ (hv i)

/-- The literal difference on every ordered overlap. -/
def difference : (∀ i, A i) →ₗ[R] (∀ i j, B i j) where
  toFun v i j := p i j (v i) - q i j (v j)
  map_add' u v := by
    ext i j
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' r v := by
    ext i j
    simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

/-- The actual image of homogeneous corrections on all whole charts. -/
def correctionImage : Submodule R (∀ i j, B i j) :=
  LinearMap.range ((difference p q).domRestrict (cochains I))

/-- The class of the full overlap error in the actual correction cokernel. -/
def obstruction (v : ∀ i, A i) : (∀ i j, B i j) ⧸ correctionImage p q I :=
  (correctionImage p q I).mkQ (difference p q v)

/-- Vanishing constructs one homogeneous cochain that corrects every overlap exactly. -/
theorem obstruction_eq_zero_iff (v : ∀ i, A i) :
    obstruction p q I v = 0 ↔
      ∃ h : ∀ i, A i, (∀ i, h i ∈ I i) ∧
        ∀ i j, p i j (v i - h i) = q i j (v j - h j) := by
  rw [obstruction, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h.val, h.property, fun i j ↦ ?_⟩
    have he := congrFun (congrFun hh i) j
    change p i j (h.val i) - q i j (h.val j) = p i j (v i) - q i j (v j) at he
    rw [map_sub, map_sub]
    linear_combination -he
  · rintro ⟨h, hh, he⟩
    refine ⟨⟨h, hh⟩, ?_⟩
    ext i j
    have hi := he i j
    rw [map_sub, map_sub] at hi
    change p i j (h i) - q i j (h j) = p i j (v i) - q i j (v j)
    linear_combination -hi

/-- Changing a lift by a full homogeneous cochain preserves its cokernel class. -/
theorem obstruction_eq_of_sub_mem (v w : ∀ i, A i) (h : ∀ i, v i - w i ∈ I i) :
    obstruction p q I v = obstruction p q I w := by
  apply sub_eq_zero.mp
  change (correctionImage p q I).mkQ (difference p q v) -
    (correctionImage p q I).mkQ (difference p q w) = 0
  rw [← map_sub, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨⟨v - w, h⟩, rfl⟩

end FLT.Mazur.HomogeneousCochainCorrection
