/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ToricHopfCharacterKernel
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Full coordinates of a toric Hopf quotient

A surjective coordinate map from a group algebra is the group algebra of its
remaining characters. The factorization retains the original map and its entire
kernel ideal; it is not a comparison merely on geometric points.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.ToricHopfCharacterKernel

variable {K G A : Type*} [Field K] [Group G] [Ring A] [HopfAlgebra K A]
  (f : MonoidAlgebra K G →ₐc[K] A)

/-- The coordinate map induced by the faithful remaining characters. -/
def quotientCoordinates : MonoidAlgebra K (G ⧸ kernel f) →ₐc[K] A :=
  (MonoidAlgebra.liftGroupLikeBialgHom (R := K) (A := A)).comp
    (MonoidAlgebra.mapDomainBialgHom K (quotientCharacter f))

/-- Each basis character maps to its original value. -/
theorem quotientCoordinates_single (g : G ⧸ kernel f) :
    quotientCoordinates f (MonoidAlgebra.single g 1) = (quotientCharacter f g).val := by
  simp [quotientCoordinates]

/-- The original coordinate homomorphism factors through exactly its character quotient. -/
theorem quotientCoordinates_factor :
    (quotientCoordinates f).comp
      (MonoidAlgebra.mapDomainBialgHom K (QuotientGroup.mk' (kernel f))) = f := by
  apply BialgHom.coe_toAlgHom_injective
  apply MonoidAlgebra.algHom_ext
  · intro g
    simp [quotientCoordinates_single, quotientCharacter_mk]
  · ext

/-- Linear independence of characters makes the whole coordinate map injective. -/
theorem quotientCoordinates_injective : Function.Injective (quotientCoordinates f) := by
  have h := (MonoidAlgebra.basis (G ⧸ kernel f) K).injective_constr_of_linearIndependent
    (R₂ := K) (quotientCharacter_linearIndependent f)
  have he : (MonoidAlgebra.basis (G ⧸ kernel f) K).constr K
      (fun g => (quotientCharacter f g).val) = (quotientCoordinates f).toAlgHom.toLinearMap := by
    apply (MonoidAlgebra.basis (G ⧸ kernel f) K).ext
    intro g
    rw [Module.Basis.constr_basis]
    exact (quotientCoordinates_single f g).symm
  rwa [he] at h

/-- Surjectivity of the original map is preserved by the faithful factorization. -/
theorem quotientCoordinates_surjective (hf : Function.Surjective f) :
    Function.Surjective (quotientCoordinates f) := by
  intro a
  obtain ⟨x, rfl⟩ := hf a
  exact ⟨MonoidAlgebra.mapDomainBialgHom K (QuotientGroup.mk' (kernel f)) x,
    DFunLike.congr_fun (quotientCoordinates_factor f) x⟩

/-- The original Hopf quotient has exactly the full algebra of the remaining characters. -/
def quotientCoordinatesEquiv (hf : Function.Surjective f) :
    MonoidAlgebra K (G ⧸ kernel f) ≃ₐc[K] A :=
  BialgEquiv.ofBijective (quotientCoordinates f)
    ⟨quotientCoordinates_injective f, quotientCoordinates_surjective f hf⟩

/-- The factorization identifies the full defining ideal, including nilpotent structure. -/
theorem coordinate_kernel_eq : RingHom.ker f.toAlgHom.toRingHom =
    RingHom.ker (MonoidAlgebra.mapDomainBialgHom K
      (QuotientGroup.mk' (kernel f))).toAlgHom.toRingHom := by
  ext x
  change f x = 0 ↔ _
  rw [← DFunLike.congr_fun (quotientCoordinates_factor f) x]
  exact map_eq_zero_iff (quotientCoordinates f) (quotientCoordinates_injective f)

end FLT.Mazur.ToricHopfCharacterKernel
