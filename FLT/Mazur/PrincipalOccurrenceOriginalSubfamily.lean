/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceSubfamilyGluing

/-!
# Open covers by prescribed original occurrence patches

The original target-compatible patches form an actual scheme open cover.
This permits recovery equalities to be tested on precisely the patches used
in the finite-stage construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  {j : κ} {μ : Type*} (c : μ → PrincipalOccurrencePatch (dst := dst) j)
  (hc : (⨆ m, (principalOccurrenceOriginalPatchOpen e (c m)).opensRange) = ⊤)

/-- The original patches, with exactly the prescribed indexing family, form an open cover. -/
def principalOccurrenceOriginalSubfamilyCover :
    (Spec (.of (Localization.Away (b j)))).OpenCover where
  I₀ := μ
  X m := principalOccurrenceOriginalPatch (a := a) (c m)
  f m := principalOccurrenceOriginalPatchOpen e (c m)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    have hz : z ∈ ⨆ m, (principalOccurrenceOriginalPatchOpen e (c m)).opensRange := by
      rw [hc]
      trivial
    obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    exact ⟨m, hm⟩

include hc in
/-- Equality on the original patch cover determines the entire original overlap morphism. -/
theorem principalOccurrenceOriginalSubfamily_hom_ext {T : Scheme.{u}}
    (g h : Spec (.of (Localization.Away (b j))) ⟶ T)
    (he : ∀ m, principalOccurrenceOriginalPatchOpen e (c m) ≫ g =
      principalOccurrenceOriginalPatchOpen e (c m) ≫ h) : g = h :=
  (principalOccurrenceOriginalSubfamilyCover e c hc).hom_ext g h he

end FLT.Mazur.FiniteTypeRelationModel
