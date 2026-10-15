/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Actual scheme splitting from disjoint open sections

A disjoint covering family of open sections identifies its whole source
with a scheme coproduct of its unchanged base. The structural map and
all original sections are recovered by exact morphism identities.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.DisjointSectionCoverSplitting
universe u v
variable {X Y : Scheme.{u}} (p : X ⟶ Y) {ι : Type v} [Small.{u} ι]
  (s : ι → (Y ⟶ X)) [∀ i, IsOpenImmersion (s i)]
  (hc : ∀ x : X, ∃ i, s i (p x) = x)
  (hd : Pairwise (fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j))))

include hc hd in
/-- The actual coproduct map is an isomorphism, with no assumed splitting datum. -/
theorem isIso_desc : IsIso (Sigma.desc s) := by
  let _ := isOpenImmersion_sigmaDesc (fun _ : ι ↦ Y) s hd
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := hc x
  refine ⟨Sigma.ι (fun _ : ι ↦ Y) i (p x), ?_⟩
  change (Sigma.ι _ i ≫ Sigma.desc s) (p x) = x
  rw [Sigma.ι_comp_desc]
  exact hi

/-- The constructed coproduct splitting of the original source. -/
def iso : (∐ fun _ : ι ↦ Y) ≅ X :=
  let _ := isIso_desc p s hc hd
  asIso (Sigma.desc s)

/-- Every original section is exactly its component inclusion under the splitting. -/
@[reassoc]
theorem ι_iso_hom (i : ι) :
    Sigma.ι (fun _ : ι ↦ Y) i ≫ (iso p s hc hd).hom = s i :=
  Sigma.ι_comp_desc s i

/-- Each original section becomes the corresponding actual coproduct inclusion. -/
@[reassoc]
theorem section_iso_inv (i : ι) :
    s i ≫ (iso p s hc hd).inv = Sigma.ι (fun _ : ι ↦ Y) i := by
  rw [← ι_iso_hom p s hc hd i, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The splitting preserves the original base projection, not only its underlying points. -/
@[reassoc]
theorem iso_hom_base (hs : ∀ i, s i ≫ p = 𝟙 Y) :
    (iso p s hc hd).hom ≫ p = Sigma.desc (fun _ : ι ↦ 𝟙 Y) := by
  apply Sigma.hom_ext
  intro i
  rw [ι_iso_hom_assoc, Sigma.ι_comp_desc, hs]

include hc hd in
/-- Independent morphisms on the actual sheets extend uniquely to the entire source. -/
theorem existsUnique_map {Z : Scheme.{u}} (a : ι → (Y ⟶ Z)) :
    ∃! b : X ⟶ Z, ∀ i, s i ≫ b = a i := by
  refine ⟨(iso p s hc hd).inv ≫ Sigma.desc a, fun i ↦ ?_, ?_⟩
  · rw [← Category.assoc, section_iso_inv, Sigma.ι_comp_desc]
  · intro b hb
    apply (cancel_epi (iso p s hc hd).hom).mp
    rw [Iso.hom_inv_id_assoc]
    apply Sigma.hom_ext
    intro i
    rw [ι_iso_hom_assoc, hb, Sigma.ι_comp_desc]

end FLT.Mazur.DisjointSectionCoverSplitting
