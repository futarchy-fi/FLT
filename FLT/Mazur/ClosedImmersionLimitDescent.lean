/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoverClosedLimit
public import FLT.Mazur.FiniteCompactOpenAffineLimit

/-!
# Global closed immersion descent for closed inverse systems

A quasi-compact finite-type map to a finitely covered scheme becomes closed
at a finite stage if it is closed on the limit. Affineness of the required
inverse images is descended first, so it is not an extra hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (g : i ⟶ j), IsClosedImmersion (D.map g)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- A closed limit of a quasi-compact finite-type map descends over a finite affine cover. -/
theorem exists_isClosedImmersion_of_finite_affine_cover (i : I)
    {Y : Scheme.{u}} (f : D.obj i ⟶ Y) [QuasiCompact f] [LocallyOfFiniteType f]
    [IsClosedImmersion (c.π.app i ≫ f)]
    {K : Type v} [Finite K] (V : K → Y.Opens)
    (hV : TopologicalSpace.IsOpenCover V) (ha : ∀ k, IsAffineOpen (V k)) :
    ∃ (j : I) (g : j ⟶ i), IsClosedImmersion (D.map g ≫ f) := by
  have hl (k : K) : IsAffineOpen (c.π.app i ⁻¹ᵁ (f ⁻¹ᵁ V k)) := by
    rw [← Scheme.Hom.comp_preimage]
    exact (ha k).preimage (c.π.app i ≫ f)
  obtain ⟨j, g, hg⟩ := exists_isAffineOpen_preimages_of_finite D c hc i
    (fun k ↦ f ⁻¹ᵁ V k) (fun k ↦ f.isCompact_preimage (ha k).isCompact) hl
  have he : c.π.app j ≫ (D.map g ≫ f) = c.π.app i ≫ f := by rw [← Category.assoc, c.w g]
  let _ : IsClosedImmersion (c.π.app j ≫ (D.map g ≫ f)) := he.symm ▸ inferInstance
  obtain ⟨k, h, hk⟩ := exists_isClosedImmersion_of_affine_preimages D c hc j (D.map g ≫ f)
    V hV ha (fun k ↦ by simpa only [Scheme.Hom.comp_preimage] using hg k)
  refine ⟨k, h ≫ g, ?_⟩
  simpa only [D.map_comp, Category.assoc] using hk

include hc in
/-- Closedness of a finite-type map to a compact scheme is detected at a finite stage. -/
theorem exists_isClosedImmersion_of_closed_limit (i : I)
    {Y : Scheme.{u}} [CompactSpace Y] (f : D.obj i ⟶ Y)
    [QuasiCompact f] [LocallyOfFiniteType f] [IsClosedImmersion (c.π.app i ≫ f)] :
    ∃ (j : I) (g : j ⟶ i), IsClosedImmersion (D.map g ≫ f) := by
  let V := Y.affineCover.finiteSubcover
  have ha (k : V.I₀) : IsAffineOpen (V.f k).opensRange := by
    let _ : IsAffine (V.X k) := inferInstanceAs (IsAffine (Spec _))
    exact isAffineOpen_opensRange (V.f k)
  exact exists_isClosedImmersion_of_finite_affine_cover D c hc i f
    (fun k ↦ (V.f k).opensRange) V.isOpenCover_opensRange ha

end FLT.Mazur.Approximation
