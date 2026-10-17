/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarQuotientResiduePresentation
public import FLT.Mazur.CompatibleErrorBaseChange

/-!
# The actual extended image in a scalar quotient presentation

The preimage of an extended quotient image is the extension of its original
preimage. Corrections remain inside that preimage, even for nonflat extension.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarQuotientImagePresentation
variable {R M D : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup D] [Module R D]
  (S : Type*) [CommRing S] [Algebra R S]

/-- Extension commutes with taking the image of an original submodule. -/
theorem map_baseChange (H : Submodule R D) (F : D →ₗ[R] M) :
    (H.map F).baseChange S = (H.baseChange S).map (F.baseChange S) := by
  have hr : H.map F = LinearMap.range (F.comp H.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hr, ← CompatibleErrorBaseChange.range_baseChange,
    LinearMap.baseChange_comp, LinearMap.range_comp]
  rfl

variable (K : Submodule R M)

/-- The scalar quotient equivalence commutes with the full extended quotient map. -/
theorem quotientEquiv_comp_mkQ :
    (ScalarQuotientResiduePresentation.quotientEquiv S K).toLinearMap ∘ₗ
      K.mkQ.baseChange S = (K.baseChange S).mkQ := by
  ext x
  rfl

/-- The scalar-extended connecting map expressed using the extended correction quotient. -/
def presentedMap (g : D →ₗ[R] M ⧸ K) :
    (S ⊗[R] D) →ₗ[S] (S ⊗[R] M) ⧸ K.baseChange S :=
  (ScalarQuotientResiduePresentation.quotientEquiv S K).toLinearMap ∘ₗ g.baseChange S

/-- Transporting a quotient image extends its original numerator submodule. -/
theorem range_presentedMap (g : D →ₗ[R] M ⧸ K) (H : Submodule R M)
    (hH : (LinearMap.range g).comap K.mkQ = H) :
    LinearMap.range (presentedMap S K g) = (H.baseChange S).map (K.baseChange S).mkQ := by
  have hmap : H.map K.mkQ = LinearMap.range g := by
    rw [← hH, Submodule.map_comap_eq_of_surjective K.mkQ_surjective]
  rw [presentedMap, LinearMap.range_comp, CompatibleErrorBaseChange.range_baseChange,
    ← hmap, map_baseChange, ← Submodule.map_comp, quotientEquiv_comp_mkQ]

/-- No new numerator ambiguity is lost: the exact preimage extends without flatness. -/
theorem preimage_presentedMap (g : D →ₗ[R] M ⧸ K) (H : Submodule R M)
    (hH : (LinearMap.range g).comap K.mkQ = H) :
    (LinearMap.range (presentedMap S K g)).comap (K.baseChange S).mkQ = H.baseChange S := by
  have hKH : K ≤ H := by
    rw [← hH]
    intro x hx
    change K.mkQ x ∈ LinearMap.range g
    have he : K.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hx
    rw [he]
    exact Submodule.zero_mem _
  rw [range_presentedMap S K g H hH, Submodule.comap_map_eq, Submodule.ker_mkQ,
    sup_eq_left.mpr (Submodule.baseChange_mono S hKH)]

/-- Vanishing of the presentation is equivalent to vanishing of the actual extended map. -/
theorem presentedMap_eq_zero_iff (g : D →ₗ[R] M ⧸ K) :
    presentedMap S K g = 0 ↔ g.baseChange S = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply (ScalarQuotientResiduePresentation.quotientEquiv S K).injective
    exact (LinearMap.congr_fun h x).trans (map_zero _).symm
  · intro h
    unfold presentedMap
    rw [h, LinearMap.comp_zero]

end FLT.Mazur.ScalarQuotientImagePresentation
