/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveChartDenominators

/-!
# Chart numerators for projective section extension

The coordinate-spectrum restriction maps agree with restriction in the original
sheaf on projective space. A section on one chart gives, after one common
coordinate power, a numerator on every chart. The numerator on the original
chart is exactly the given section. Pairwise compatibility away from that chart
and gluing to a twisted global section are separate steps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate spectrum covers exactly its standard chart. -/
lemma chartMap_image_top (i : ι) : chartMap R ι i ''ᵁ ⊤ = chart R ι i := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact Proj.opensRange_awayι (grading R ι) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) (by decide)

/-- Sections in affine coordinates identified with sections on the actual chart. -/
def chartSectionsIso (F : (space R ι).Modules) (i : ι) :
    Γ(chartModule R ι F i, ⊤) ≅ Γ(F, chart R ι i) :=
  F.restrictAppIso (chartMap R ι i) ⊤ ≪≫
    F.presheaf.mapIso (eqToIso (chartMap_image_top R ι i).symm).op

/-- The overlap localization map is restriction in the original projective sheaf. -/
lemma overlapSectionsIso_restriction (F : (space R ι).Modules) (i j : ι)
    (s : chartSections R ι F i) :
    (overlapSectionsIso R ι F i j).hom (chartOverlapRestriction R ι F i j s) =
      F.presheaf.map (homOfLE inf_le_left).op ((chartSectionsIso R ι F i).hom s) := by
  simp only [chartOverlapRestriction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    overlapPrincipalEquiv, LinearEquiv.symm_trans_apply]
  change F.presheaf.map _
    (F.presheaf.map _ (F.presheaf.map _
      (F.presheaf.map _ (F.presheaf.map _ s)))) =
    F.presheaf.map _ (F.presheaf.map _ s)
  simp only [← Functor.map_comp_apply]
  congr 1

/-- The overlap coordinate-ring action as scalars in the original structure sheaf. -/
def overlapScalarHom (i j : ι) :
    overlapRing R ι i j →+* Γ(space R ι, chart R ι i ⊓ chart R ι j) :=
  (((Scheme.ΓSpecIso (.of (overlapRing R ι i j))).inv ≫
    ((overlapMap R ι i j).appIso ⊤).inv) ≫
      (space R ι).presheaf.map
        (eqToHom (overlapMap_image_top R ι i j).symm).op).hom

/-- The overlap comparison intertwines coordinate scalars and geometric scalars. -/
lemma overlapSectionsIso_smul (F : (space R ι).Modules) (i j : ι)
    (r : overlapRing R ι i j) (s : overlapSections R ι F i j) :
    (overlapSectionsIso R ι F i j).hom (r • s) =
      overlapScalarHom R ι i j r • (overlapSectionsIso R ι F i j).hom s := by
  exact F.val.map_smul (eqToHom (overlapMap_image_top R ι i j).symm).op _ s

/-- Restrict a section from the second chart, expressed in first-chart overlap coordinates. -/
def chartToOtherOverlap (F : (space R ι).Modules) (i j : ι) :
    chartSections R ι F i →+ overlapSections R ι F j i :=
  (overlapSectionsIso R ι F j i).inv.hom.comp
    ((F.presheaf.map (homOfLE inf_le_right).op).hom.comp
      (chartSectionsIso R ι F i).hom.hom)

/-- The second-chart restriction has the expected value in the original sheaf. -/
lemma overlapSectionsIso_otherRestriction (F : (space R ι).Modules) (i j : ι)
    (s : chartSections R ι F i) :
    (overlapSectionsIso R ι F j i).hom (chartToOtherOverlap R ι F i j s) =
      F.presheaf.map (homOfLE inf_le_right).op ((chartSectionsIso R ι F i).hom s) := by
  exact ConcreteCategory.congr_hom (overlapSectionsIso R ι F j i).inv_hom_id _

/-- On a repeated chart both descriptions are the same restriction. -/
lemma chartToOtherOverlap_self (F : (space R ι).Modules) (i : ι)
    (s : chartSections R ι F i) :
    chartToOtherOverlap R ι F i i s = chartOverlapRestriction R ι F i i s := by
  apply (ConcreteCategory.bijective_of_isIso (overlapSectionsIso R ι F i i).hom).injective
  rw [overlapSectionsIso_otherRestriction, overlapSectionsIso_restriction]

/-- All charts have numerators for the restriction of one section, with one exponent. -/
theorem sectionExtension_chartNumerators [Finite ι] (F : (space R ι).Modules)
    [F.IsFinitePresentation] (i : ι) (s : chartSections R ι F i) :
    ∃ (N : ℕ) (t : ∀ j, chartSections R ι F j), t i = s ∧
      ∀ j, chartOverlapRestriction R ι F j i (t j) =
        coordinate R ι j i ^ N • chartToOtherOverlap R ι F i j s := by
  classical
  obtain ⟨N, t, ht⟩ := overlapFamily_clearDenominators R ι F (fun j ↦ j) (fun _ ↦ i)
    (fun j ↦ chartToOtherOverlap R ι F i j s)
  let t' : ∀ j, chartSections R ι F j := fun j ↦ if h : j = i then h.symm ▸ s else t j
  refine ⟨N, t', ?_, ?_⟩
  · simp [t']
  · intro j
    by_cases h : j = i
    · subst j
      simp [t', coordinate_self, chartToOtherOverlap_self]
    · simpa only [t', dite_eq_right h] using ht j

/-- Numerators persist at every larger degree, keeping the original chart fixed. -/
theorem sectionExtension_eventually_chartNumerators [Finite ι]
    (F : (space R ι).Modules) [F.IsFinitePresentation]
    (i : ι) (s : chartSections R ι F i) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : ∀ j, chartSections R ι F j,
      t i = s ∧ ∀ j, chartOverlapRestriction R ι F j i (t j) =
        coordinate R ι j i ^ n • chartToOtherOverlap R ι F i j s := by
  obtain ⟨N, t, hi, ht⟩ := sectionExtension_chartNumerators R ι F i s
  refine ⟨N, fun n hn ↦ ⟨fun j ↦ coordinate R ι j i ^ (n - N) • t j, ?_, ?_⟩⟩
  · simp only [coordinate_self, one_pow, one_smul, hi]
  · intro j
    exact chartOverlap_raise_numerator R ι F j i _ (t j) (ht j) hn

/-- In the original sheaf the numerators restrict to the coordinate power times `s`. -/
theorem sectionExtension_chartNumerators_geometric [Finite ι]
    (F : (space R ι).Modules) [F.IsFinitePresentation]
    (i : ι) (s : chartSections R ι F i) :
    ∃ (N : ℕ) (t : ∀ j, chartSections R ι F j), t i = s ∧ ∀ j,
      F.presheaf.map (homOfLE inf_le_left).op ((chartSectionsIso R ι F j).hom (t j)) =
        overlapScalarHom R ι j i (toOverlap R ι j i (coordinate R ι j i)) ^ N •
          F.presheaf.map (homOfLE inf_le_right).op ((chartSectionsIso R ι F i).hom s) := by
  obtain ⟨N, t, hi, ht⟩ := sectionExtension_chartNumerators R ι F i s
  refine ⟨N, t, hi, fun j ↦ ?_⟩
  have h := congrArg (overlapSectionsIso R ι F j i).hom (ht j)
  simpa only [overlapSectionsIso_restriction, overlapSections_pow_smul,
    overlapSectionsIso_smul, map_pow, overlapSectionsIso_otherRestriction] using h

/-- Starting from an actual chart section requires no chosen affine-coordinate data. -/
theorem sectionExtension_openChartNumerators [Finite ι]
    (F : (space R ι).Modules) [F.IsFinitePresentation]
    (i : ι) (s : Γ(F, chart R ι i)) :
    ∃ (N : ℕ) (t : ∀ j, Γ(F, chart R ι j)), t i = s ∧ ∀ j,
      F.presheaf.map (homOfLE inf_le_left).op (t j) =
        overlapScalarHom R ι j i (toOverlap R ι j i (coordinate R ι j i)) ^ N •
          F.presheaf.map (homOfLE inf_le_right).op s := by
  obtain ⟨N, t, hi, ht⟩ := sectionExtension_chartNumerators_geometric R ι F i
    ((chartSectionsIso R ι F i).inv s)
  have he : (chartSectionsIso R ι F i).hom ((chartSectionsIso R ι F i).inv s) = s :=
    ConcreteCategory.congr_hom (chartSectionsIso R ι F i).inv_hom_id s
  refine ⟨N, fun j ↦ (chartSectionsIso R ι F j).hom (t j), ?_, ?_⟩
  · exact (congrArg (chartSectionsIso R ι F i).hom hi).trans he
  · intro j
    simpa only [he] using ht j

end FLT.Mazur.ProjectiveSpace
