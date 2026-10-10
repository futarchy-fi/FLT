/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientFamilySupport

/-!
# Exact universal factorization through the ambient support open

A parameter factors through the constructed Hilbert support open precisely
when the actual represented closed family's map to the original ambient
factors through the chosen ambient open. The support open pulls back to the
intrinsic support locus of each actual family, over every scheme base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (f : AmbientSchemeParameters R I d K s)

/-- The represented family is the actual base change of the full universal family. -/
theorem ambientSchemeClassification_familyPullback :
    quotientSchemeFamilyBaseChange R I d K (ambientHilbertStructure R I d K) s f.val f.property
        (ambientUniversalFamily R I d K) = ambientSchemeClassification R I d K s f := by
  have h := ambientSchemeClassification_natural R I d K
    (ambientHilbertStructure R I d K) s f.val f.property ⟨𝟙 _, Category.id_comp _⟩
  have he : ambientSchemeParameterBaseChange R I d K
      (ambientHilbertStructure R I d K) s f.val f.property ⟨𝟙 _, Category.id_comp _⟩ = f := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [he] at h
  exact h.symm

/-- The Hilbert support open pulls back to the intrinsic support open of every family. -/
theorem ambientHilbertSupportOpen_pullback :
    quotientFamilySupportOpen R I d K s (ambientSchemeClassification R I d K s f) U =
      f.val ⁻¹ᵁ ambientHilbertSupportOpen R I d K U := by
  rw [← ambientSchemeClassification_familyPullback R I d K s f]
  exact quotientFamilySupportOpen_baseChange R I d K (ambientHilbertStructure R I d K)
    (ambientUniversalFamily R I d K) U s f.val f.property

/-- The parameter range lies in the support open exactly when the whole family lies in U. -/
theorem range_subset_ambientHilbertSupportOpen_iff :
    Set.range f.val ⊆ ambientHilbertSupportOpen R I d K U ↔
      Set.range (quotientFamilyAmbientMap R I d K s
        (ambientSchemeClassification R I d K s f)) ⊆ U := by
  let J := ambientSchemeClassification R I d K s f
  have hU := ambientHilbertSupportOpen_pullback R I d K U s f
  constructor
  · rintro h _ ⟨z, rfl⟩
    apply (mem_quotientFamilySupportOpen R I d K s J U
      ((J.val.subschemeι ≫ pullback.fst _ _) z)).mp
      (show (J.val.subschemeι ≫ pullback.fst _ _) z ∈
        quotientFamilySupportOpen R I d K s J U from ?_) z rfl
    rw [hU]
    exact h ⟨_, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    change x ∈ f.val ⁻¹ᵁ ambientHilbertSupportOpen R I d K U
    rw [← hU]
    exact (mem_quotientFamilySupportOpen R I d K s J U x).mpr fun z _ ↦ h ⟨z, rfl⟩

/-- Exact scheme factorization: the parameter enters the support open iff the family enters U. -/
theorem ambientHilbertSupportOpen_factorization_iff :
    (∃ a : X ⟶ (ambientHilbertSupportOpen R I d K U).toScheme,
      a ≫ (ambientHilbertSupportOpen R I d K U).ι = f.val) ↔
      ∃ b : (ambientSchemeClassification R I d K s f).val.subscheme ⟶ U.toScheme,
        b ≫ U.ι = quotientFamilyAmbientMap R I d K s
          (ambientSchemeClassification R I d K s f) := by
  rw [factors_open_iff, factors_open_iff]
  exact range_subset_ambientHilbertSupportOpen_iff R I d K U s f

end FLT.Mazur.HilbertChart
