/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageCoefficientSystems
public import FLT.Mazur.PolygonInfinitesimalSectionRings
public import FLT.Mazur.SectionGradedLinePullback

/-!
# The original boundary and its section ring under coefficient change

The cartesian marked family comparison preserves the full Cartier ideal.
Its canonical positive-line pullback gives maps on every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SectionGradedSum SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
  (m n : ℕ) (h : 2 ≤ n)

/-- The full original Cartier boundary is retained by coefficient change. -/
theorem boundaryIdeal_stageCoefficientFamily :
    (boundaryIdeal R m n h).comap (stageCoefficientFamily f m n h) =
      boundaryIdeal S m n h :=
  section_prod_comap_of_cartesian (stageCoefficientFamily_isPullback f m n h)
    Finset.univ _ _ (fun i ↦ marking_base S m n h i)
    (fun i ↦ marking_base R m n h i) (fun i ↦ marking_stageCoefficientFamily f m n h i)

/-- The actual Cartier ideal-module comparison is invertible. -/
instance boundaryIdeal_coefficient_isIso :
    IsIso (idealModulePullbackHom (boundaryIdeal R m n h)
      (stageCoefficientFamily f m n h)) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (boundaryIdeal_cartier R m n h).1
  rw [boundaryIdeal_stageCoefficientFamily]
  exact (boundaryIdeal_cartier S m n h).1

/-- The canonical comparison of the original positive boundary lines. -/
def coefficientBoundaryLineIso :
    (pullback (stageCoefficientFamily f m n h)).obj (boundaryLine R m n h) ≅
      boundaryLine S m n h :=
  divisorLinePullbackIsoOfEq _ (boundaryIdeal_cartier R m n h).1
    (boundaryIdeal_cartier S m n h).1 (boundaryIdeal_stageCoefficientFamily f m n h)

/-- Coefficient pullback on all tensor degrees of the actual boundary section ring. -/
def coefficientBoundarySections :
    boundaryGradedSections R n h m →+* boundaryGradedSections S n h m :=
  SectionGradedLinePullback.ringHom (stageCoefficientFamily f m n h)
    (coefficientBoundaryLineIso f m n h)

/-- The homogeneous formula retains the actual line pullback comparison. -/
theorem coefficientBoundarySections_of (d : ℕ) (s : Piece (boundaryLine R m n h) ⊤ d) :
    coefficientBoundarySections f m n h (of (boundaryLine R m n h) ⊤ d s) =
      of (boundaryLine S m n h) ⊤ d
        (SectionGradedLinePullback.sectionMap (stageCoefficientFamily f m n h)
          (coefficientBoundaryLineIso f m n h) d ⊤ s) :=
  SectionGradedLinePullback.ringHom_of _ _ d s

/-- Every tensor degree is preserved by actual coefficient pullback. -/
theorem coefficientBoundarySections_mem_grade {d : ℕ} {s : boundaryGradedSections R n h m}
    (hs : s ∈ grade (boundaryLine R m n h) ⊤ d) :
    coefficientBoundarySections f m n h s ∈ grade (boundaryLine S m n h) ⊤ d := by
  obtain ⟨s, rfl⟩ := hs
  exact ⟨_, (coefficientBoundarySections_of f m n h d s).symm⟩

end FLT.Mazur.PolygonInfinitesimalStages
