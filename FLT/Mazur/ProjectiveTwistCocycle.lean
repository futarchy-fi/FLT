/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSpaceCharts

/-!
# The unit cocycle for projective twists

The coordinate ratios multiply on triple overlaps. Their integer powers give
transition units in the structure sheaf on the standard chart intersections.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogeneous coordinates on a triple overlap. -/
abbrev tripleRing (i j k : ι) := Away (grading R ι) (X i * X j * X k)

/-- Restriction from the first pair to a triple overlap. -/
def toTriple₁₂ (i j k : ι) : overlapRing R ι i j →+* tripleRing R ι i j k :=
  awayMap _ (isHomogeneous_X R k) rfl

/-- Restriction from the second pair to a triple overlap. -/
def toTriple₂₃ (i j k : ι) : overlapRing R ι j k →+* tripleRing R ι i j k :=
  awayMap _ (isHomogeneous_X R i) (by ring)

/-- Restriction from the outer pair to a triple overlap. -/
def toTriple₁₃ (i j k : ι) : overlapRing R ι i k →+* tripleRing R ι i j k :=
  awayMap _ (isHomogeneous_X R j) (by ring)

/-- The coordinate fractions satisfy the cocycle law. -/
lemma ratioUnit_cocycle (i j k : ι) :
    Units.map (toTriple₁₂ R ι i j k).toMonoidHom (ratioUnit R ι i j) *
      Units.map (toTriple₂₃ R ι i j k).toMonoidHom (ratioUnit R ι j k) =
    Units.map (toTriple₁₃ R ι i j k).toMonoidHom (ratioUnit R ι i k) := by
  apply Units.ext
  change toTriple₁₂ R ι i j k (ratioUnit R ι i j) *
    toTriple₂₃ R ι i j k (ratioUnit R ι j k) =
    toTriple₁₃ R ι i j k (ratioUnit R ι i k)
  simp only [ratioUnit_val, toOverlap_coordinate, toTriple₁₂, toTriple₂₃, toTriple₁₃,
    awayMap_mk]
  apply val_injective
  simp only [val_mul, Away.val_mk, pow_one, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- All integer twists satisfy the same overlap cocycle. -/
lemma transitionUnit_cocycle (n : ℤ) (i j k : ι) :
    Units.map (toTriple₁₂ R ι i j k).toMonoidHom (transitionUnit R ι n i j) *
      Units.map (toTriple₂₃ R ι i j k).toMonoidHom (transitionUnit R ι n j k) =
    Units.map (toTriple₁₃ R ι i j k).toMonoidHom (transitionUnit R ι n i k) := by
  simp only [transitionUnit, map_zpow, ← mul_zpow, ratioUnit_cocycle]

/-- Reverse the order of the factors defining an overlap ring. -/
def overlapSwap (i j : ι) : overlapRing R ι j i →+* overlapRing R ι i j :=
  awayMap _ (isHomogeneous_one (σ := ι) (R := R)) (by ring)

/-- Swapping the charts inverts the ratio. -/
lemma ratioUnit_swap (i j : ι) :
    Units.map (overlapSwap R ι i j).toMonoidHom (ratioUnit R ι j i) =
      (ratioUnit R ι i j)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  change overlapSwap R ι i j (ratioUnit R ι j i) * (ratioUnit R ι i j) = 1
  simp only [ratioUnit_val, toOverlap_coordinate, overlapSwap, awayMap_mk]
  apply val_injective
  simp only [val_mul, val_one, Away.val_mk, pow_one, mul_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- Swapping charts inverts every integer transition coefficient. -/
lemma transitionUnit_swap (n : ℤ) (i j : ι) :
    Units.map (overlapSwap R ι i j).toMonoidHom (transitionUnit R ι n j i) =
      (transitionUnit R ι n i j)⁻¹ := by
  simp only [transitionUnit, map_zpow, ratioUnit_swap, inv_zpow]

/-- Restriction of units in the structure sheaf. -/
def restrictUnits {U V : (space R ι).Opens} (h : V ≤ U) :
    Γ(space R ι, U)ˣ →* Γ(space R ι, V)ˣ :=
  Units.map ((space R ι).presheaf.map (homOfLE h).op).hom.toMonoidHom

/-- Unit restriction respects composition of open inclusions. -/
lemma restrictUnits_comp {U V W : (space R ι).Opens} (h : V ≤ U) (h' : W ≤ V)
    (s : Γ(space R ι, U)ˣ) :
    restrictUnits R ι h' (restrictUnits R ι h s) = restrictUnits R ι (h'.trans h) s := by
  apply Units.ext
  exact congrArg (fun f ↦ f.hom (s : Γ(space R ι, U)))
    ((space R ι).presheaf.map_comp (homOfLE h).op (homOfLE h').op).symm

/-- The homogeneous localization comparison also compares units. -/
lemma awayUnit_restrict {f g x : MvPolynomial ι R} {d : ℕ}
    (hg : g ∈ grading R ι d) (hx : x = f * g) (s : (Away (grading R ι) f)ˣ) :
    restrictUnits R ι (Proj.basicOpen_mono _ _ _ ⟨g, hx⟩)
        (Units.map (Proj.awayToSection (grading R ι) f).hom.toMonoidHom s) =
      Units.map (Proj.awayToSection (grading R ι) x).hom.toMonoidHom
        (Units.map (awayMap (grading R ι) hg hx).toMonoidHom s) := by
  apply Units.ext
  exact congrArg (fun φ ↦ φ.hom (s : Away (grading R ι) f))
    (Proj.awayMap_awayToSection (grading R ι) hg hx).symm

/-- The actual intersection of three standard opens. -/
abbrev tripleOpen (i j k : ι) : (space R ι).Opens :=
  chart R ι i ⊓ chart R ι j ⊓ chart R ι k

lemma tripleOpen_eq (i j k : ι) :
    tripleOpen R ι i j k = Proj.basicOpen (grading R ι) (X i * X j * X k) := by
  simp only [tripleOpen, chart, Proj.basicOpen_mul]

lemma tripleOpen_le₁₂ (i j k : ι) :
    tripleOpen R ι i j k ≤ Proj.basicOpen (grading R ι) (X i * X j) := by
  rw [← chart_inf]
  exact inf_le_left

lemma tripleOpen_le₂₃ (i j k : ι) :
    tripleOpen R ι i j k ≤ Proj.basicOpen (grading R ι) (X j * X k) := by
  rw [← chart_inf]
  exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

lemma tripleOpen_le₁₃ (i j k : ι) :
    tripleOpen R ι i j k ≤ Proj.basicOpen (grading R ι) (X i * X k) := by
  rw [← chart_inf]
  exact le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- Map triple-overlap coordinates to sections on the actual intersection. -/
def tripleUnitsToSection (i j k : ι) :
    (tripleRing R ι i j k)ˣ →* Γ(space R ι, tripleOpen R ι i j k)ˣ :=
  (restrictUnits R ι (tripleOpen_eq R ι i j k).le).comp
    (Units.map (Proj.awayToSection (grading R ι) (X i * X j * X k)).hom.toMonoidHom)

lemma transitionSection_restrict₁₂ (n : ℤ) (i j k : ι) :
    restrictUnits R ι (tripleOpen_le₁₂ R ι i j k) (transitionSection R ι n i j) =
      tripleUnitsToSection R ι i j k
        (Units.map (toTriple₁₂ R ι i j k).toMonoidHom (transitionUnit R ι n i j)) := by
  rw [tripleUnitsToSection, MonoidHom.comp_apply, toTriple₁₂, ← awayUnit_restrict]
  exact (restrictUnits_comp R ι _ _ _).symm

lemma transitionSection_restrict₂₃ (n : ℤ) (i j k : ι) :
    restrictUnits R ι (tripleOpen_le₂₃ R ι i j k) (transitionSection R ι n j k) =
      tripleUnitsToSection R ι i j k
        (Units.map (toTriple₂₃ R ι i j k).toMonoidHom (transitionUnit R ι n j k)) := by
  rw [tripleUnitsToSection, MonoidHom.comp_apply, toTriple₂₃, ← awayUnit_restrict]
  exact (restrictUnits_comp R ι _ _ _).symm

lemma transitionSection_restrict₁₃ (n : ℤ) (i j k : ι) :
    restrictUnits R ι (tripleOpen_le₁₃ R ι i j k) (transitionSection R ι n i k) =
      tripleUnitsToSection R ι i j k
        (Units.map (toTriple₁₃ R ι i j k).toMonoidHom (transitionUnit R ι n i k)) := by
  rw [tripleUnitsToSection, MonoidHom.comp_apply, toTriple₁₃, ← awayUnit_restrict]
  exact (restrictUnits_comp R ι _ _ _).symm

/-- The twisting transitions satisfy the structure-sheaf cocycle on triple intersections. -/
lemma transitionSection_cocycle (n : ℤ) (i j k : ι) :
    restrictUnits R ι (tripleOpen_le₁₂ R ι i j k) (transitionSection R ι n i j) *
      restrictUnits R ι (tripleOpen_le₂₃ R ι i j k) (transitionSection R ι n j k) =
    restrictUnits R ι (tripleOpen_le₁₃ R ι i j k) (transitionSection R ι n i k) := by
  rw [transitionSection_restrict₁₂, transitionSection_restrict₂₃,
    transitionSection_restrict₁₃, ← map_mul, transitionUnit_cocycle]

/-- Reversing the order does not change the overlap open. -/
lemma overlapOpen_swap (i j : ι) :
    Proj.basicOpen (grading R ι) (X i * X j) =
      Proj.basicOpen (grading R ι) (X j * X i) := by rw [mul_comm]

/-- On the same overlap, reversed transition sections are inverse units. -/
lemma transitionSection_swap (n : ℤ) (i j : ι) :
    restrictUnits R ι (overlapOpen_swap R ι i j).le (transitionSection R ι n j i) =
      (transitionSection R ι n i j)⁻¹ := by
  have h := awayUnit_restrict R ι (f := X j * X i) (x := X i * X j)
    (isHomogeneous_one ι R) (by ring) (transitionUnit R ι n j i)
  change _ = Units.map _ (Units.map (overlapSwap R ι i j).toMonoidHom
    (transitionUnit R ι n j i)) at h
  simpa only [transitionSection, transitionUnit_swap, map_inv] using h

@[simp]
lemma transitionSection_zero (i j : ι) : transitionSection R ι 0 i j = 1 := by
  simp only [transitionSection, transitionUnit_zero, map_one]

@[simp]
lemma transitionSection_self (n : ℤ) (i : ι) : transitionSection R ι n i i = 1 := by
  simp only [transitionSection, transitionUnit_self, map_one]

/-- The transition unit, with its domain written as an intersection of charts. -/
def twistTransition (n : ℤ) (i j : ι) :
    Γ(space R ι, chart R ι i ⊓ chart R ι j)ˣ :=
  restrictUnits R ι (chart_inf R ι i j).le (transitionSection R ι n i j)

@[simp]
lemma twistTransition_self (n : ℤ) (i : ι) : twistTransition R ι n i i = 1 := by
  simp only [twistTransition, transitionSection_self, map_one]

@[simp]
lemma twistTransition_zero (i j : ι) : twistTransition R ι 0 i j = 1 := by
  simp only [twistTransition, transitionSection_zero, map_one]

/-- The unit cocycle in intersection notation, ready for module descent. -/
lemma twistTransition_cocycle (n : ℤ) (i j k : ι) :
    restrictUnits R ι (inf_le_left : tripleOpen R ι i j k ≤ _)
        (twistTransition R ι n i j) *
      restrictUnits R ι (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        tripleOpen R ι i j k ≤ _) (twistTransition R ι n j k) =
    restrictUnits R ι (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      tripleOpen R ι i j k ≤ _) (twistTransition R ι n i k) := by
  simpa only [twistTransition, restrictUnits_comp] using transitionSection_cocycle R ι n i j k

/-- Reversing the overlap in intersection notation gives the inverse transition. -/
lemma twistTransition_swap (n : ℤ) (i j : ι) :
    restrictUnits R ι (inf_comm (chart R ι i) (chart R ι j)).le
      (twistTransition R ι n j i) = (twistTransition R ι n i j)⁻¹ := by
  simp only [twistTransition, restrictUnits_comp]
  rw [← map_inv, ← transitionSection_swap, restrictUnits_comp]

end FLT.Mazur.ProjectiveSpace
