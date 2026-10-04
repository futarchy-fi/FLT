/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicNonvanishing
public import FLT.Mazur.ModuleSectionProjectiveChart

/-!
# Actual projective chart maps for the polygon cubic family

Enumerate the finite family by a finite ordinal. Each denominator's genuine
nonvanishing open maps to its standard projective chart, with the exact
inverse-image opens needed for gluing. Equality of different local morphisms
on intersections remains to be proved before there is a global projective map.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Enumerate the pair and the three coordinates per component by a finite ordinal. -/
def cubicCoordinateEquiv (n : ℕ) : Fin (n * 3 + 1 + 1) ≃ CubicIndex.{u} n :=
  (finCongr (by rw [cubicIndex_card]; omega)).trans (Fintype.equivFin _).symm

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The actual finite family, indexed by standard projective coordinates. -/
def finiteCubicFamily (i : Fin (n * 3 + 1 + 1)) : Γ(polygonLine K n hn p q h a 3, ⊤) :=
  cubicFamily K n hn p q h a (cubicCoordinateEquiv n i)

/-- Denominator opens after finite reindexing. -/
def finiteCubicOpen (i : Fin (n * 3 + 1 + 1)) : C.left.Opens :=
  cubicOpen K n hn p q h a (cubicCoordinateEquiv n i)

/-- Finite reindexing retains the proved open covering. -/
lemma iSup_finiteCubicOpen : ⨆ i, finiteCubicOpen K n hn p q h a i = ⊤ := by
  simpa only [finiteCubicOpen, Equiv.iSup_comp] using iSup_cubicOpen K n hn p q h a

/-- Coefficients act by the polygon's actual structure morphism, restricted to the open. -/
def cubicOpenScalars (U : C.left.Opens) : K →+* Γ(C.left, U) :=
  (C.left.presheaf.map (homOfLE le_top).op).hom.comp
    (C.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)

/-- The genuine morphism from a denominator open into finite-dimensional projective space. -/
def cubicProjectiveChartMorphism (i : Fin (n * 3 + 1 + 1)) :
    (finiteCubicOpen K n hn p q h a i).toScheme ⟶
      ProjectiveSpace.space K (Fin (n * 3 + 1 + 1)) :=
  sectionProjectiveChartMorphism (polygonLine K n hn p q h a 3) (n * 3 + 1)
    (finiteCubicFamily K n hn p q h a) i (finiteCubicOpen K n hn p q h a i) le_rfl
      (cubicOpenScalars K (finiteCubicOpen K n hn p q h a i))

/-- The inverse image of every projective chart is the expected denominator intersection. -/
lemma cubicProjectiveChartMorphism_preimage_image (i j : Fin (n * 3 + 1 + 1)) :
    (finiteCubicOpen K n hn p q h a i).ι ''ᵁ
      (cubicProjectiveChartMorphism K n hn p q h a i ⁻¹ᵁ
        ProjectiveSpace.chart K (Fin (n * 3 + 1 + 1)) j) =
      finiteCubicOpen K n hn p q h a i ⊓ finiteCubicOpen K n hn p q h a j :=
  sectionProjectiveChartMorphism_preimage_image (polygonLine K n hn p q h a 3)
    (n * 3 + 1) (finiteCubicFamily K n hn p q h a) i _ le_rfl _ j

end FLT.Mazur.PolygonCubicSections
