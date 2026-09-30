/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Standard charts of polynomial projective space

We use Mathlib's Proj of the standard graded polynomial ring. The coordinate
opens cover it and have the usual homogeneous localization coordinate rings.
The overlap rings carry the invertible ratios used for twisting modules.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u v

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type v)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard grading of the homogeneous coordinate ring. -/
abbrev grading := homogeneousSubmodule ι R

/-- Polynomial projective space, with homogeneous coordinates indexed by `ι`.
Taking `ι = Fin (d + 1)` gives projective `d`-space. -/
abbrev space : Scheme := Proj (grading R ι)

/-- The standard open `D₊(Xᵢ)`. -/
def chart (i : ι) : (space R ι).Opens := Proj.basicOpen (grading R ι) (X i)

/-- The coordinate ring of the standard open. -/
abbrev chartRing (i : ι) := Away (grading R ι) (X i)

/-- The standard chart is affine, using the existing Proj chart. -/
def chartIso (i : ι) :
    (chart R ι i).toScheme ≅ Spec (.of (chartRing R ι i)) :=
  Proj.basicOpenIsoSpec _ _ (isHomogeneous_X R i) (by decide)

/-- Standard coordinates generate the polynomial ring over its degree-zero part. -/
lemma adjoin_coordinates :
    Algebra.adjoin (grading R ι 0) (Set.range (X : ι → MvPolynomial ι R)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact (Algebra.adjoin (grading R ι 0) (Set.range X)).algebraMap_mem
      ⟨C r, isHomogeneous_C ι r⟩
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- The standard coordinate opens cover polynomial projective space. -/
lemma iSup_chart : ⨆ i, chart R ι i = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ X
    (fun i ↦ ⟨1, isHomogeneous_X R i⟩) (adjoin_coordinates R ι)

/-- Every point belongs to a standard chart. -/
lemma exists_mem_chart (x : space R ι) : ∃ i, x ∈ chart R ι i := by
  have hx : x ∈ ⨆ i, chart R ι i := by rw [iSup_chart]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- The ring of an overlap `D₊(Xᵢ Xⱼ)`. -/
abbrev overlapRing (i j : ι) := Away (grading R ι) (X i * X j)

/-- The product basic open is exactly the intersection of standard charts. -/
lemma chart_inf (i j : ι) :
    chart R ι i ⊓ chart R ι j = Proj.basicOpen (grading R ι) (X i * X j) :=
  (Proj.basicOpen_mul _ _ _).symm

/-- Affine coordinates on the overlap of two standard charts. -/
def overlapIso (i j : ι) :
    (Proj.basicOpen (grading R ι) (X i * X j)).toScheme ≅
      Spec (.of (overlapRing R ι i j)) :=
  Proj.basicOpenIsoSpec _ _ ((isHomogeneous_X R i).mul (isHomogeneous_X R j))
    (by decide)

/-- The affine coordinate `Xⱼ/Xᵢ`. -/
def coordinate (i j : ι) : chartRing R ι i :=
  Away.mk _ (isHomogeneous_X R i) 1 (X j) (isHomogeneous_X R j)

/-- The coordinate of a chart's own variable is one. -/
@[simp]
lemma coordinate_self (i : ι) : coordinate R ι i i = 1 := by
  apply val_injective
  simp only [coordinate, Away.val_mk, val_one, pow_one]
  exact Localization.mk_self ⟨X i, Submonoid.mem_powers _⟩

/-- Restriction from a chart to its overlap with another chart. -/
def toOverlap (i j : ι) : chartRing R ι i →+* overlapRing R ι i j :=
  awayMap _ (isHomogeneous_X R j) rfl

/-- In the overlap ring the ratio is represented by `Xⱼ²/(Xᵢ Xⱼ)`. -/
lemma toOverlap_coordinate (i j : ι) :
    toOverlap R ι i j (coordinate R ι i j) =
      Away.mk _ ((isHomogeneous_X R i).mul (isHomogeneous_X R j)) 1
        (X j * X j) ((isHomogeneous_X R j).mul (isHomogeneous_X R j)) := by
  dsimp only [toOverlap, coordinate]
  simpa only [pow_one] using
    (awayMap_mk (grading R ι) (isHomogeneous_X R j)
      (f := X i) rfl 1 (isHomogeneous_X R i) (X j) (isHomogeneous_X R j))

/-- The overlap is the principal localization of a chart at `Xⱼ/Xᵢ`. -/
lemma overlap_isLocalization (i j : ι) :
    let := (toOverlap R ι i j).toAlgebra
    IsLocalization.Away (coordinate R ι i j) (overlapRing R ι i j) := by
  dsimp only [toOverlap, coordinate]
  simpa only [Away.isLocalizationElem, pow_one] using
    (Away.isLocalization_mul (isHomogeneous_X R i) (isHomogeneous_X R j)
      (x := X i * X j) rfl (by decide : (1 : ℕ) ≠ 0))

/-- The coordinate ratio becomes a unit on the overlap. -/
lemma isUnit_ratio (i j : ι) :
    IsUnit (toOverlap R ι i j (coordinate R ι i j)) := by
  let := (toOverlap R ι i j).toAlgebra
  let := overlap_isLocalization R ι i j
  exact IsLocalization.Away.algebraMap_isUnit (coordinate R ι i j)

/-- The unit `Xⱼ/Xᵢ` in the overlap coordinate ring. -/
def ratioUnit (i j : ι) : (overlapRing R ι i j)ˣ :=
  (isUnit_ratio R ι i j).unit

@[simp]
lemma ratioUnit_val (i j : ι) :
    (ratioUnit R ι i j : overlapRing R ι i j) =
      toOverlap R ι i j (coordinate R ι i j) :=
  (isUnit_ratio R ι i j).unit_spec

/-- The ratio on a repeated chart is the identity. -/
@[simp]
lemma ratioUnit_self (i : ι) : ratioUnit R ι i i = 1 := by
  apply Units.ext
  simp only [ratioUnit_val, coordinate_self, map_one, Units.val_one]

/-- The transition coefficient `(Xⱼ/Xᵢ)ⁿ` for every integer twist. -/
def transitionUnit (n : ℤ) (i j : ι) : (overlapRing R ι i j)ˣ :=
  ratioUnit R ι i j ^ n

@[simp]
lemma transitionUnit_zero (i j : ι) : transitionUnit R ι 0 i j = 1 := zpow_zero _

@[simp]
lemma transitionUnit_one (i j : ι) :
    transitionUnit R ι 1 i j = ratioUnit R ι i j := zpow_one _

lemma transitionUnit_add (m n : ℤ) (i j : ι) :
    transitionUnit R ι (m + n) i j =
      transitionUnit R ι m i j * transitionUnit R ι n i j := zpow_add _ _ _

lemma transitionUnit_neg (n : ℤ) (i j : ι) :
    transitionUnit R ι (-n) i j = (transitionUnit R ι n i j)⁻¹ := zpow_neg _ _

/-- The transition on a repeated chart is the identity for every twist. -/
@[simp]
lemma transitionUnit_self (n : ℤ) (i : ι) : transitionUnit R ι n i i = 1 := by
  simp only [transitionUnit, ratioUnit_self, one_zpow]

/-- Multiplication by the transition coefficient identifies the two free
rank-one modules over the overlap ring. -/
def transitionEquiv (n : ℤ) (i j : ι) :
    overlapRing R ι i j ≃ₗ[overlapRing R ι i j] overlapRing R ι i j :=
  LinearEquiv.smulOfUnit (transitionUnit R ι n i j)

/-- The linear transition map is multiplication by `(Xⱼ/Xᵢ)ⁿ`. -/
lemma transitionEquiv_apply (n : ℤ) (i j : ι) (s : overlapRing R ι i j) :
    transitionEquiv R ι n i j s = (transitionUnit R ι n i j : overlapRing R ι i j) * s :=
  rfl

/-- Transition coefficients as units of the actual structure-sheaf sections
on the overlap in Proj. -/
def transitionSection (n : ℤ) (i j : ι) :
    Γ(space R ι, Proj.basicOpen (grading R ι) (X i * X j))ˣ :=
  Units.map (Proj.awayToSection (grading R ι) (X i * X j)).hom.toMonoidHom
    (transitionUnit R ι n i j)

/-- The unit on the overlap is the image of the homogeneous fraction. -/
lemma transitionSection_one (i j : ι) :
    (transitionSection R ι 1 i j :
      Γ(space R ι, Proj.basicOpen (grading R ι) (X i * X j))) =
    (Proj.awayToSection (grading R ι) (X i * X j)).hom
      (Away.mk _ ((isHomogeneous_X R i).mul (isHomogeneous_X R j)) 1
        (X j * X j) ((isHomogeneous_X R j).mul (isHomogeneous_X R j))) := by
  change (Proj.awayToSection (grading R ι) (X i * X j)).hom
    (transitionUnit R ι 1 i j : overlapRing R ι i j) = _
  rw [transitionUnit_one, ratioUnit_val, toOverlap_coordinate]

/-- Adding twists multiplies their transition sections. -/
lemma transitionSection_add (m n : ℤ) (i j : ι) :
    transitionSection R ι (m + n) i j =
      transitionSection R ι m i j * transitionSection R ι n i j := by
  simp only [transitionSection, transitionUnit_add, map_mul]

end FLT.Mazur.ProjectiveSpace
