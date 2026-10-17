/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SubmoduleQuotientScalarReduction
public import FLT.Mazur.SubmoduleReductionKernel

/-!
# The second reduction kernel in original representatives

For a submodule of a quotient, reduction of its inclusion has a separate
kernel. Pulling its injectivity criterion back to the original module keeps
both the corrections and the internal multiples of the actual image preimage.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.QuotientImageReduction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (J : Ideal R) (K : Submodule R M) (Q : Submodule R (M ⧸ K))

/-- Image multiples lift to corrections plus internal preimage multiples. -/
theorem comap_smul :
    (J • Q).comap K.mkQ = K ⊔ J • Q.comap K.mkQ := by
  have hmap : (Q.comap K.mkQ).map K.mkQ = Q :=
    Submodule.map_comap_eq_of_surjective K.mkQ_surjective Q
  calc
    (J • Q).comap K.mkQ = ((J • Q.comap K.mkQ).map K.mkQ).comap K.mkQ := by
      rw [Submodule.map_smul'', hmap]
    _ = K ⊔ J • Q.comap K.mkQ := by
      rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_comm]

/-- The lost image classes pull back to the intersection with corrections plus ambient multiples. -/
theorem comap_reduction_intersection :
    (Q ⊓ J • (⊤ : Submodule R (M ⧸ K))).comap K.mkQ =
      Q.comap K.mkQ ⊓ (K ⊔ J • (⊤ : Submodule R M)) := by
  rw [Submodule.comap_inf, RelativeSubmoduleQuotient.comap_quotient_smul_top]

/-- Injectivity of image reduction is precisely the second original intersection identity. -/
theorem inclusion_injective_iff_preimage :
    Function.Injective (SubmoduleReduction.inclusion J Q) ↔
      Q.comap K.mkQ ⊓ (K ⊔ J • (⊤ : Submodule R M)) =
        K ⊔ J • Q.comap K.mkQ := by
  rw [SubmoduleReduction.inclusion_injective_iff]
  constructor
  · intro h
    have he := congrArg (Submodule.comap K.mkQ) h
    rwa [comap_reduction_intersection, comap_smul] at he
  · intro h
    apply Submodule.comap_injective_of_surjective K.mkQ_surjective
    rwa [comap_reduction_intersection, comap_smul]

/-- Vanishing of the quotient image after reduction is a separate preimage containment. -/
theorem residual_vanishing_iff_preimage :
    Q ≤ J • (⊤ : Submodule R (M ⧸ K)) ↔
      Q.comap K.mkQ ≤ K ⊔ J • (⊤ : Submodule R M) := by
  rw [← RelativeSubmoduleQuotient.comap_quotient_smul_top J K]
  constructor
  · exact Submodule.comap_mono
  · intro h x hx
    obtain ⟨y, rfl⟩ := K.mkQ_surjective x
    exact h hx

end FLT.Mazur.QuotientImageReduction
