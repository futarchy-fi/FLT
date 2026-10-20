/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenCoefficientRestriction
public import FLT.Mazur.OpenSectionTopComparison

/-!
# Gluing actual invariant coefficients on an open cover

Compatible full coefficients give a unique original global section. Invariance
is proved on a cover of the entire original relation, retaining nilpotents.
No affineness, finite rank or algebraization hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantOpenCoefficientGluing
open InvariantOpenCoefficientRestriction SchemeEffectiveEpiSections Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (hcover : iSup U = ⊤)

/-- The top-section coordinate of restriction is the ordinary sheaf restriction. -/
theorem inclusion_coordinates (V : X.Opens) (s : Γ(X, ⊤)) :
    V.topIso.hom (V.ι.appTop s) = X.presheaf.map (homOfLE le_top).op s := by
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

include hcover in
/-- Full sections are detected on any cover by actual source opens. -/
theorem section_ext (s t : Γ(X, ⊤))
    (h : ∀ i, (U i).ι.appTop s = (U i).ι.appTop t) : s = t := by
  apply X.sheaf.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) hcover.ge
  intro i
  change X.presheaf.map (homOfLE le_top).op s =
    X.presheaf.map (homOfLE le_top).op t
  rw [← inclusion_coordinates, ← inclusion_coordinates, h i]

include hcover in
/-- Compatible sections of the open subschemes glue in the original source. -/
theorem existsUnique_section (s : ∀ i, Γ((U i).toScheme, ⊤))
    (hs : ∀ i j, (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).appTop (s i) =
      (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop (s j)) :
    ∃! t : Γ(X, ⊤), ∀ i, (U i).ι.appTop t = s i := by
  have hex : ∃! t : Γ(X, ⊤), ∀ i,
      X.presheaf.map (homOfLE le_top).op t = (U i).topIso.hom (s i) := by
    apply X.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hcover.ge
    intro i j
    change X.presheaf.map (homOfLE inf_le_left).op ((U i).topIso.hom (s i)) =
      X.presheaf.map (homOfLE inf_le_right).op ((U j).topIso.hom (s j))
    rw [topIso_hom_restriction, topIso_hom_restriction, hs i j]
  obtain ⟨t, ht, _⟩ := hex
  have ht' (i : ι) : (U i).ι.appTop t = s i := by
    apply (U i).topIso.commRingCatIsoToRingEquiv.injective
    change (U i).topIso.hom ((U i).ι.appTop t) = (U i).topIso.hom (s i)
    rw [inclusion_coordinates, ht i]
  exact ⟨t, ht', fun z hz ↦ section_ext U hcover z t (fun i ↦ (hz i).trans (ht' i).symm)⟩

variable {D A : Scheme.{0}} (p q : D ⟶ A) (V : ι → A.Opens)
  (hV : ∀ i, p ⁻¹ᵁ V i = q ⁻¹ᵁ V i) (hcov : iSup V = ⊤)

include hcov in
/-- The first endpoint preimages cover the full relation, not merely its reduction. -/
theorem relation_cover : (⨆ i, p ⁻¹ᵁ V i) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show p z ∈ iSup V from hcov.symm ▸ trivial)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

include hV hcov in
/-- Local full invariant values force the entire original relation equation. -/
theorem invariant_of_local (s : Γ(A, ⊤))
    (hs : ∀ i, (V i).ι.appTop s ∈ coefficients p q (V i) (hV i)) :
    s ∈ compatibleFunctions p q := by
  apply section_ext (fun i ↦ p ⁻¹ᵁ V i) (relation_cover p V hcov)
  intro i
  have he := hs i
  change (p.resLE (V i) _ le_rfl).appTop ((V i).ι.appTop s) =
    (q.resLE (V i) _ (hV i).le).appTop ((V i).ι.appTop s) at he
  change ((p ⁻¹ᵁ V i).ι ≫ p).appTop s = ((p ⁻¹ᵁ V i).ι ≫ q).appTop s
  rw [← p.resLE_comp_ι le_rfl,
    ← q.resLE_comp_ι (hV i).le]
  exact he

include hcov in
/-- Compatible invariant local coefficients construct a unique actual invariant section. -/
theorem existsUnique_invariant (s : ∀ i, coefficients p q (V i) (hV i))
    (hs : ∀ i j,
      restriction p q (V i) (V i ⊓ V j) (hV i)
          (inf_invariant p q (V i) (V j) (hV i) (hV j)) inf_le_left (s i) =
        restriction p q (V j) (V i ⊓ V j) (hV j)
          (inf_invariant p q (V i) (V j) (hV i) (hV j)) inf_le_right (s j)) :
    ∃! t : compatibleFunctions p q, ∀ i, (V i).ι.appTop t.val = (s i).val := by
  obtain ⟨t, ht, hu⟩ := existsUnique_section V hcov (fun i ↦ (s i).val)
    (fun i j ↦ congrArg Subtype.val (hs i j))
  have hm : t ∈ compatibleFunctions p q := invariant_of_local p q V hV hcov t
    (fun i ↦ by rw [ht i]; exact (s i).property)
  exact ⟨⟨t, hm⟩, ht, fun z hz ↦ Subtype.ext (hu z.val hz)⟩

end FLT.Mazur.InvariantOpenCoefficientGluing
