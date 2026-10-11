/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperDenseOpenExtension

/-!
# Proper curves with a common dense open

A common dense open determines an isomorphism between proper integral separated
schemes with valuation stalks. Both inverse maps are constructed by proper
extension, and their composites are checked on the given dense open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur

universe u

/-- Extend a map whose domain is presented by a dominant open immersion. -/
theorem exists_openImmersion_extension_of_valuation_stalks
    {S X Z U : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    [∀ x : X, ValuationRing (X.presheaf.stalk x)]
    (q : X ⟶ S) (r : Z ⟶ S) [IsProper r]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j] (g : U ⟶ Z)
    (hg : g ≫ r = j ≫ q) :
    ∃ f : X ⟶ Z, f ≫ r = q ∧ j ≫ f = g := by
  obtain ⟨f, hf, _⟩ := existsUnique_denseOpen_extension_of_valuation_stalks q r
    j.opensRange j.denseRange (j.isoOpensRange.inv ≫ g) (by
      rw [Category.assoc, hg, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp])
  refine ⟨f, hf.1, ?_⟩
  rw [← j.isoOpensRange_hom_ι, Category.assoc, hf.2, Iso.hom_inv_id_assoc]

/-- An extension from a common dense open is an isomorphism of proper valuation-stalk schemes. -/
theorem isIso_of_common_denseOpen
    {S X Z U : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    [IsIntegral Z] [Z.IsSeparated]
    [∀ z : Z, ValuationRing (Z.presheaf.stalk z)]
    (q : X ⟶ S) (r : Z ⟶ S) [IsProper q]
    (j : U ⟶ X) [IsDominant j]
    (k : U ⟶ Z) [IsOpenImmersion k] [IsDominant k]
    (f : X ⟶ Z) (hf : f ≫ r = q) (hjk : j ≫ f = k) : IsIso f := by
  obtain ⟨g, _, hgj⟩ := exists_openImmersion_extension_of_valuation_stalks r q k j
    (by rw [← hjk, Category.assoc, hf])
  have hfg : f ≫ g = 𝟙 X := by
    apply ext_of_isDominant j
    rw [← Category.assoc, hjk, hgj, Category.comp_id]
  have hgf : g ≫ f = 𝟙 Z := by
    apply ext_of_isDominant k
    rw [← Category.assoc, hgj, hjk, Category.comp_id]
  exact ⟨⟨g, hfg, hgf⟩⟩

end FLT.Mazur
