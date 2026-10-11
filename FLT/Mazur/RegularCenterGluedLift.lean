/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterDoubleOverlap
public import FLT.Mazur.BlowupReesContraction

/-!
# Gluing the actual regular-center fraction lifts

An original ring map whose center becomes a regular principal ideal lifts to
the original Rees Proj. The map is glued on the complete quotient-open cover,
using the proved equality on actual scheme intersections. Its contraction is
the original ring map and its restrictions are the constructed fraction lifts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.RegularCenter

open BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d) {ι : Type*} [Finite ι]
  (g : ι → A) (hg : ∀ i, g i ∈ I) (hspan : Ideal.span (Set.range g) = I)

/-- Gluing all actual quotient-open lifts gives a morphism into the original Rees Proj. -/
def gluedLift : Spec (.of B) ⟶ proj I :=
  (quotientCover I φ d hI hd g hg hspan).openCover.glueMorphisms
    (fun i => quotientOpenToProj I φ d hI hd (g i) (hg i))
    (fun i j => quotientOpenToProj_pullback_overlap I φ d hI hd (g i) (hg i) (g j) (hg j))

/-- The glued lift retains the actual fraction-chart map on every quotient-open member. -/
@[reassoc] theorem quotientCover_gluedLift (i : ι) :
    (quotientCover I φ d hI hd g hg hspan).f i ≫ gluedLift I φ d hI hd g hg hspan =
      quotientOpenToProj I φ d hI hd (g i) (hg i) :=
  (quotientCover I φ d hI hd g hg hspan).openCover.ι_glueMorphisms _ _ i

/-- Contraction of each local lift is exactly the original ring map restricted to that open. -/
@[reassoc] theorem quotientOpenToProj_contraction (a : A) (ha : a ∈ I) :
    quotientOpenToProj I φ d hI hd a ha ≫ contraction I =
      Spec.map (CommRingCat.ofHom (algebraMap B (QuotientOpen I φ d hI a ha))) ≫
        Spec.map (CommRingCat.ofHom φ) := by
  rw [quotientOpenToProj, Category.assoc, fractionChartInclusion_contraction]
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  exact quotientOpenLift_base I φ d hI a ha hd z

/-- The glued lift contracts to the given original morphism on the entire input scheme. -/
@[reassoc] theorem gluedLift_contraction :
    gluedLift I φ d hI hd g hg hspan ≫ contraction I = Spec.map (CommRingCat.ofHom φ) := by
  apply (quotientCover I φ d hI hd g hg hspan).openCover.hom_ext
  intro i
  change (quotientCover I φ d hI hd g hg hspan).f i ≫
    gluedLift I φ d hI hd g hg hspan ≫ contraction I =
      (quotientCover I φ d hI hd g hg hspan).f i ≫ Spec.map (CommRingCat.ofHom φ)
  rw [quotientCover_gluedLift_assoc, quotientOpenToProj_contraction]
  rfl

end FLT.Mazur.RegularCenter
