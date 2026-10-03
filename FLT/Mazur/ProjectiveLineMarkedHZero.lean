/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineMarkedSectionGluing
public import FLT.Mazur.ModuleCohomology
public import FLT.Mazur.ProjectiveLineConstantSections
/-!
# Zeroth cohomology of a positive marked divisor power

The actual Ext-based H0 of O(m[a]) is linearly equivalent to polynomials
of degree at most m. The field action is the one induced by the specified
projective-line structure morphism, and the map uses the existing chart
coordinates of genuine global sections.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineMarkedHZero
open FCurve ProjectiveLineMarkedSectionTransition ProjectiveLineMarkedSectionInjective
open ProjectiveLineMarkedSectionGluing ProjectiveLineMarkedPullbackCoordinates
open ProjectiveLineMarkedDualCoordinates ProjectiveLineMarkedCharts
variable (K : Type u) [Field K] (a : Kˣ) (m : ℕ)
/-- The left polynomial coordinate of an actual global section. -/
def sectionPolynomial (s : Γ(line K a m, ⊤)) : K[X] :=
  (coordinateRing K).symm (chartSectionsCoordinate K a (ProjectiveLine.left K) a
    (left_ideal K a) m (pullGlobal (ProjectiveLine.left K) (line K a m) s))
/-- Evaluation of a section morphism recovers its existing polynomial coordinate. -/
lemma sectionPolynomial_hom (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    sectionPolynomial K a m (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) =
      leftPolynomial K a m s := by
  apply (coordinateRing K).injective
  rw [sectionPolynomial, RingEquiv.apply_symm_apply]
  exact (polynomial_coordinate K a m _ _ _ s).symm
/-- The actual section coordinate is additive. -/
lemma sectionPolynomial_add (s t : Γ(line K a m, ⊤)) :
    sectionPolynomial K a m (s + t) = sectionPolynomial K a m s + sectionPolynomial K a m t := by
  simp only [sectionPolynomial, map_add]
/-- Coordinates respect the scalar action induced by the structure morphism. -/
lemma sectionPolynomial_smul (c : K) (s : Γ(line K a m, ⊤)) :
    sectionPolynomial K a m (structureScalarMap (ProjectiveLine.toBase K) c • s) =
      c • sectionPolynomial K a m s := by
  have hc : (coordinateRing K).symm ((ProjectiveLine.left K).appTop
      (structureScalarMap (ProjectiveLine.toBase K) c)) = Polynomial.C c :=
    ProjectiveLineConstantSections.coordinate_scalar K false c
  unfold sectionPolynomial
  rw [map_smulₛₗ, LinearEquiv.map_smul, smul_eq_mul, map_mul, hc]
  exact (Polynomial.smul_eq_C_mul c).symm
/-- Genuine degree-zero sheaf cohomology of the marked divisor power. -/
abbrev H0 := ModuleScalarH (ProjectiveLine.toBase K) (line K a m) 0
/-- The bounded polynomial of an actual cohomology class. -/
def bounded (x : H0 K a m) : Polynomial.degreeLT K (m + 1) :=
  boundedPolynomial K a m (globalSectionHom (line K a m)
    (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x))
/-- The bounded coordinate is the polynomial of the corresponding global section. -/
lemma bounded_val (x : H0 K a m) : (bounded K a m x).val =
    sectionPolynomial K a m (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x) := by
  rw [← globalSectionHom_top (line K a m)
    (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x), sectionPolynomial_hom]
  rfl
/-- The linear polynomial-coordinate map on actual H0. -/
def polynomialMap : H0 K a m →ₗ[K] Polynomial.degreeLT K (m + 1) where
  toFun := bounded K a m
  map_add' x y := by
    apply Subtype.ext
    simp only [bounded_val, map_add, Submodule.coe_add]
    exact sectionPolynomial_add K a m _ _
  map_smul' c x := by
    apply Subtype.ext
    change (bounded K a m (c • x)).val = c • (bounded K a m x).val
    rw [bounded_val, bounded_val]
    have he := (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m)).map_smul c x
    change moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) (c • x) =
      structureScalarMap (ProjectiveLine.toBase K) c •
        moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x at he
    rw [he, sectionPolynomial_smul]
/-- Gluing and section extensionality make the H0 coordinate map bijective. -/
lemma polynomialMap_bijective : Function.Bijective (polynomialMap K a m) := by
  constructor
  · intro x y h
    apply (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m)).injective
    have he := boundedPolynomial_injective K a m h
    have hh := congrArg (fun f ↦ f.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) he
    simpa only [globalSectionHom_top] using hh
  · intro p
    obtain ⟨s, hs⟩ := boundedPolynomial_surjective K a m p
    refine ⟨(moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m)).symm
      (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))), ?_⟩
    change boundedPolynomial K a m (globalSectionHom (line K a m) _) = p
    rw [LinearEquiv.apply_symm_apply]
    have he : globalSectionHom (line K a m)
        (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) = s := by
      apply globalSection_hom_ext
      exact globalSectionHom_top _ _
    rw [he, hs]
/-- Actual H0 is linearly equivalent to bounded polynomials. -/
def polynomialEquiv : H0 K a m ≃ₗ[K] Polynomial.degreeLT K (m + 1) :=
  LinearEquiv.ofBijective (polynomialMap K a m) (polynomialMap_bijective K a m)
end FLT.Mazur.ProjectiveLineMarkedHZero
