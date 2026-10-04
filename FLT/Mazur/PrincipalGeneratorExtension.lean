/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalSectionExtension

/-!
# Extending a principal-open generator with its exact nonvanishing locus

One extra scalar factor makes a global numerator vanish off the principal
open. Its generator open is then exactly the image of the original section's
generator open, so affine generator opens remain affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{0}} {M : X.Modules} [CompactSpace X] [X.IsSeparated]

/-- A section on a principal open extends with exactly the same generator locus. -/
theorem exists_principal_generator_extension (hM : LocallyFreeRankOne M)
    (r : Γ(X, ⊤)) (U : X.Opens) (hU : U = X.basicOpen r)
    (s : Γ(M.restrict U.ι, ⊤)) :
    ∃ t : Γ(M, ⊤), sectionGeneratorOpen M t =
      U.ι ''ᵁ sectionGeneratorOpen (M.restrict U.ι) s := by
  let := hM.isFinitePresentation M
  let B := U.ι ''ᵁ (⊤ : U.toScheme.Opens)
  have hB : B = X.basicOpen r := by simp [B, hU]
  obtain ⟨n, t, ht⟩ := exists_principalSection_numerator M r B hB s
  let a := U.ι.appTop r
  let s₀ : Γ(M, B) := (M.restrictAppIso U.ι ⊤).hom s
  have hscalar (k : ℕ) : (show Γ(M, B) from a ^ k • s) =
      (X.presheaf.map B.leTop.op r) ^ k • s₀ := by
    change (U.ι.appIso ⊤).inv (a ^ k) • s₀ = _
    rw [Scheme.Opens.ι_appIso]
    rfl
  have ha : U.toScheme.basicOpen a = ⊤ := by
    rw [← Scheme.Hom.preimage_basicOpen_top, ← hU]
    simp
  let σ := r • t
  have hσ : M.presheaf.map B.leTop.op σ = a ^ (n + 1) • s := by
    refine Eq.trans ?_ (hscalar (n + 1)).symm
    dsimp [σ]
    rw [M.map_smul, ht, smul_smul, pow_succ']
    rfl
  have hopen : U.ι ⁻¹ᵁ sectionGeneratorOpen M σ =
      sectionGeneratorOpen (M.restrict U.ι) s := by
    rw [← sectionGeneratorOpen_restrict hM U.ι σ]
    erw [hσ]
    rw [sectionGeneratorOpen_smul, U.toScheme.basicOpen_pow a (Nat.succ_pos n), ha, top_inf_eq]
  have hle : sectionGeneratorOpen M σ ≤ U := by
    rw [sectionGeneratorOpen_smul, hU]
    exact inf_le_left
  refine ⟨σ, ?_⟩
  rw [← hopen, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hle]

end FLT.Mazur.FCurve
