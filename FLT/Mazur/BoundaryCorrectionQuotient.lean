/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Colon

/-!
# The quotient by boundary-preserving corrections

For a surjective boundary map, quotienting raw numerators by compatible
numerators and boundary-zero corrections gives exactly the boundary cokernel.
The scalar annihilator therefore allows corrections depending on the numerator.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryCorrectionQuotient
variable {R M B : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup B] [Module R B] (C : Submodule R M) (β : M →ₗ[R] B)

/-- Raw numerators whose boundary value admits a compatible representative. -/
def correctable : Submodule R M := (C.map β).comap β

/-- Correctable numerators are precisely compatible numerators plus boundary-zero corrections. -/
theorem correctable_eq_sup : correctable C β = C ⊔ LinearMap.ker β :=
  Submodule.comap_map_eq β C

/-- A correction is an actual element of the unchanged boundary kernel. -/
theorem mem_correctable_iff (a : M) :
    a ∈ correctable C β ↔ ∃ w : M, β w = 0 ∧ a - w ∈ C := by
  change β a ∈ C.map β ↔ _
  constructor
  · rintro ⟨v, hv, he⟩
    exact ⟨a - v, by rw [map_sub, he, sub_self], by simpa using hv⟩
  · rintro ⟨w, hw, hv⟩
    exact ⟨a - w, hv, by rw [map_sub, hw, sub_zero]⟩

/-- The raw boundary map followed by its compatible cokernel. -/
def obstruction : M →ₗ[R] B ⧸ C.map β := (C.map β).mkQ.comp β

/-- The kernel is computed before any localization or passage to residue fields. -/
theorem ker_obstruction : LinearMap.ker (obstruction C β) = correctable C β := by
  ext a
  exact Submodule.Quotient.mk_eq_zero (C.map β)

/-- Raw surjectivity gives surjectivity onto the actual boundary obstruction. -/
theorem obstruction_surjective (hβ : Function.Surjective β) :
    Function.Surjective (obstruction C β) :=
  (C.map β).mkQ_surjective.comp hβ

/-- The corrected raw quotient is canonically the full boundary cokernel. -/
def quotientEquiv (hβ : Function.Surjective β) :
    (M ⧸ correctable C β) ≃ₗ[R] B ⧸ C.map β :=
  (Submodule.quotEquivOfEq _ _ (ker_obstruction C β).symm).trans
    ((obstruction C β).quotKerEquivOfSurjective (obstruction_surjective C β hβ))

/-- The canonical equivalence sends each original numerator to its boundary class. -/
theorem quotientEquiv_mk (hβ : Function.Surjective β) (a : M) :
    quotientEquiv C β hβ ((correctable C β).mkQ a) = (C.map β).mkQ (β a) := rfl

/-- Exact annihilation is equivalent to constructing a boundary-zero correction for each input. -/
theorem mem_boundary_annihilator_iff (hβ : Function.Surjective β) (x : R) :
    x ∈ Module.annihilator R (B ⧸ C.map β) ↔
      ∀ a : M, ∃ w : M, β w = 0 ∧ x • a - w ∈ C := by
  rw [Submodule.annihilator_quotient, Submodule.mem_colon]
  constructor
  · intro h a
    apply (mem_correctable_iff C β (x • a)).mp
    change β (x • a) ∈ C.map β
    rw [map_smul]
    exact h (β a) (Set.mem_univ _)
  · intro h b _
    obtain ⟨a, rfl⟩ := hβ b
    have ha := (mem_correctable_iff C β (x • a)).mpr (h a)
    change β (x • a) ∈ C.map β at ha
    simpa only [map_smul] using ha

/-- The corrected quotient and boundary cokernel have the same exact scalar annihilator. -/
theorem annihilator_eq (hβ : Function.Surjective β) :
    Module.annihilator R (M ⧸ correctable C β) =
      Module.annihilator R (B ⧸ C.map β) := by
  ext x
  rw [mem_boundary_annihilator_iff C β hβ,
    Submodule.annihilator_quotient, Submodule.mem_colon]
  simp only [Set.mem_univ, forall_const, mem_correctable_iff]

end FLT.Mazur.BoundaryCorrectionQuotient
