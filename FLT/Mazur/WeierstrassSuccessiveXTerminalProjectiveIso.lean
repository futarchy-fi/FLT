/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalAffineIntersection

/-!
# The original equality-depth terminal component is a projective line

Normalize only the first affine coordinate by its original unit scale.
The exact Laurent intersection and full affine cover identify the actual
conic/Laurent gluing with the fixed projective line, preserving both marks.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) = n)
local notation "K" => ResidueField R
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => laurentConicComponent_constant_isUnit D k b6 h6 hp
local notation "P" => laurentConicComponent D k hk b3 b4 b6 h3 h4 h6 hp
local notation "l" => laurentConicComponentConic D k hk b3 b4 b6 h3 h4 h6 hp
local notation "r" => laurentConicComponentTorus D k hk b3 b4 b6 h3 h4 h6 hp
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "f" => laurentConicComponentFirstAffine D k hk b3 b4 b6 h3 h4 h6 hp
local notation "g" => laurentConicComponentSecondAffine D k hk b3 b4 b6 h3 h4 h6 hp

local notation "E" => ProjectiveLine.chartScalingIso K (Inv.inv (IsUnit.unit hc))

/-- Normalization gives exactly the standard projective-line intersection square. -/
theorem laurentConicComponentNormalized_isPullback :
    IsPullback (ProjectiveLine.overlapLeft K) (ProjectiveLine.overlapRight K)
      ((E).hom ≫ f) g := by
  apply (laurentConicComponentAffine_isPullback D k hk b3 b4 b6 h3 h4 h6 hp).of_iso'
    (Iso.refl _) E (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, ProjectiveLine.scaledOverlapLeft]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The two normalized full affine charts still exhaust the actual component. -/
theorem laurentConicComponentNormalized_cover (x : P) :
    (∃ y, ((E).hom ≫ f) y = x) ∨ ∃ z, g z = x := by
  rcases laurentConicComponentAffine_cover D k hk b3 b4 b6 h3 h4 h6 hp x with
    ⟨y, hy⟩ | h
  · left
    refine ⟨(E).inv y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]
    exact hy
  · exact Or.inr h

/-- The actual full terminal component, identified with the fixed projective line. -/
def laurentConicComponentProjectiveIso : ProjectiveLine.scheme K ≅ P :=
  SchemeOpenPushout.coverIso (ProjectiveLine.overlapLeft K) (ProjectiveLine.overlapRight K)
    ((E).hom ≫ f) g
    (laurentConicComponentNormalized_isPullback D k hk b3 b4 b6 h3 h4 h6 hp)
    (laurentConicComponentNormalized_cover D k hk b3 b4 b6 h3 h4 h6 hp)
local notation "J" => laurentConicComponentProjectiveIso D k hk b3 b4 b6 h3 h4 h6 hp

/-- The first projective chart retains the original first coordinate scale. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_left :
    ProjectiveLine.left K ≫ (J).hom = (E).hom ≫ f :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The second projective chart is the original completed second parameter. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_right :
    ProjectiveLine.right K ≫ (J).hom = g :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

/-- Zero is exactly the original first ordered attachment. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_zero :
    ProjectiveLine.zero K ≫ (J).hom =
      laurentConicComponentFirstSection D k hk b3 b4 b6 h3 h4 h6 hp := by
  rw [ProjectiveLine.zero, Category.assoc, laurentConicComponentProjectiveIso_left]
  change ProjectiveLine.chartZero K ≫ ProjectiveLine.chartScaling K ((hc).unit)⁻¹ ≫ f = _
  rw [ProjectiveLine.chartZero_chartScaling_assoc, laurentConicComponentFirstAffine_origin]

/-- Infinity is exactly the original second ordered attachment. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_infinity :
    ProjectiveLine.infinity K ≫ (J).hom =
      laurentConicComponentSecondSection D k hk b3 b4 b6 h3 h4 h6 hp := by
  rw [ProjectiveLine.infinity, Category.assoc, laurentConicComponentProjectiveIso_right,
    laurentConicComponentSecondAffine_origin]

/-- The entire standard Laurent torus is the original terminal torus, without rescaling. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_torus :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ (J).hom = r := by
  rw [← Category.assoc, ProjectiveLine.overlap_condition, Category.assoc,
    laurentConicComponentProjectiveIso_right, laurentConicComponentSecondAffine_torus]

end FLT.Mazur.WeierstrassSuccessiveX
