/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCompactOpenAffineLimit

/-!
# Descending affineness and coverage for prescribed opens

If the inverse images of finitely many prescribed compact opens form an affine
cover of the limit, those same opens form an affine cover after refinement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ i, CompactSpace (D.obj i)]

include hc in
/-- Prescribed compact opens become an affine cover at one common later stage. -/
theorem exists_affine_cover_preimages_of_finite {K : Type v} [Finite K]
    (i : I) (U : K → (D.obj i).Opens)
    (hU : ∀ k, IsCompact (U k : Set (D.obj i)))
    (haff : ∀ k, IsAffineOpen (c.π.app i ⁻¹ᵁ U k))
    (hcover : (⨆ k, c.π.app i ⁻¹ᵁ U k) = ⊤) :
    ∃ (j : I) (f : j ⟶ i),
      (∀ k, IsAffineOpen (D.map f ⁻¹ᵁ U k)) ∧ (⨆ k, D.map f ⁻¹ᵁ U k) = ⊤ := by
  obtain ⟨j, f, hj⟩ := exists_isAffineOpen_preimages_of_finite D c hc i U hU haff
  have htop : c.π.app j ⁻¹ᵁ (⨆ k, D.map f ⁻¹ᵁ U k) = ⊤ := by
    simp_rw [Scheme.Hom.preimage_iSup, ← Scheme.Hom.comp_preimage, c.w]
    exact hcover
  obtain ⟨l, g, hg⟩ := exists_map_eq_top D c hc (⨆ k, D.map f ⁻¹ᵁ U k) htop
  refine ⟨l, g ≫ f, fun k ↦ ?_, ?_⟩
  · simpa only [Functor.map_comp, Scheme.Hom.comp_preimage] using (hj k).preimage (D.map g)
  · simpa only [Scheme.Hom.preimage_iSup, Functor.map_comp, Scheme.Hom.comp_preimage] using hg

end FLT.Mazur.Approximation
