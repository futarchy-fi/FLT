/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineRechart

/-!
# Recovering section lines from equal projective points

Equality of actual projective morphisms supplies a morphism to the genuine
chart intersection. Its coordinate ring map makes the transition ratio a
unit, allowing both lines to be compared in one fixed coordinate chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type u} [CommRing R] [CommRing S] {ι : Type u}

/-- Equal projective chart maps force the other coordinate ratio to be a unit. -/
lemma chartPoint_coordinate_isUnit (i j : ι)
    (p : Spec (.of S) ⟶ Spec (.of (chartRing R ι i)))
    (q : Spec (.of S) ⟶ Spec (.of (chartRing R ι j)))
    (h : p ≫ chartMap R ι i = q ≫ chartMap R ι j) :
    IsUnit ((Spec.preimage p).hom (coordinate R ι i j)) := by
  let l := (chartOverlapIsPullback R ι i j).lift p q h
  have hl : l ≫ Spec.map (CommRingCat.ofHom
      (chartOverlapLeft R ι i j).toRingHom) = p :=
    (chartOverlapIsPullback R ι i j).lift_fst p q h
  have hr : CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom ≫
      Spec.preimage l = Spec.preimage p := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hl]
  have he := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hr) (coordinate R ι i j)
  exact he ▸ (isUnit_ratio R ι i j).map (Spec.preimage l).hom

/-- The generator has a unit coordinate wherever its projective point is in that chart. -/
lemma sectionLinePoint_coordinate_isUnit (f : R →+* S) (i j : ι)
    (L : NormalizedSectionLine.Chart S ι i) (N : NormalizedSectionLine.Chart S ι j)
    (h : sectionLinePoint R ι f i L = sectionLinePoint R ι f j N) :
    IsUnit (NormalizedSectionLine.generator S ι i L j) := by
  have hu := chartPoint_coordinate_isUnit i j
    ((sectionLineChartEquiv R ι f i).symm L).val
    ((sectionLineChartEquiv R ι f j).symm N).val h
  rw [← sectionLineChartEquiv_generator R ι f i
    ((sectionLineChartEquiv R ι f i).symm L) j, Equiv.apply_symm_apply] at hu
  exact hu

/-- An actual projective point uniquely determines its section submodule across charts. -/
lemma sectionLinePoint_eq_iff (f : R →+* S) (i j : ι)
    (L : NormalizedSectionLine.Chart S ι i) (N : NormalizedSectionLine.Chart S ι j) :
    sectionLinePoint R ι f i L = sectionLinePoint R ι f j N ↔ L.val = N.val := by
  constructor
  · intro h
    let hu := sectionLinePoint_coordinate_isUnit f i j L N h
    let P := NormalizedSectionLine.rechart i j L hu.unit hu.unit_spec.symm
    have hp : sectionLinePoint R ι f i L = sectionLinePoint R ι f j P :=
      NormalizedSectionLine.projectivePoint_change S ι f i j L P rfl
    have he : P = N := sectionLinePoint_injective R ι f j (hp.symm.trans h)
    exact congrArg Subtype.val he
  · exact NormalizedSectionLine.projectivePoint_change S ι f i j L N

end FLT.Mazur.ProjectiveSpace
