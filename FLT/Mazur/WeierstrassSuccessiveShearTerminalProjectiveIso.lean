/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalAffineIntersection

/-!
# The original equality-depth terminal component is a projective line

Normalize only the first affine coordinate by its original unit scale.
The exact Laurent intersection and full affine cover identify the actual
conic/Laurent gluing with the fixed projective line, preserving both marks.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveShearTerminal
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [Field S] [Algebra R S] (ρ : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : ρ ^ 2 + algebraMap R S W.a₁ * ρ - algebraMap R S W.a₂ = 0)
  (hc : IsUnit (algebraMap R S b6)) (u : Sˣ)
  (hu : (u : S) = (rootShearCurve (W.map (algebraMap R S)) ρ).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) ρ
local notation "K" => S
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S b6
local notation "ha" => Eq.mp (congrArg IsUnit hu) (Units.isUnit u)
local notation "P" => laurentConicComponent W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "l" => laurentConicComponentConic W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "r" => laurentConicComponentTorus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "f" => laurentConicComponentFirstAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "g" => laurentConicComponentSecondAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

local notation "E" => ProjectiveLine.chartScalingIso K (Inv.inv (IsUnit.unit hc))

/-- Normalization gives exactly the standard projective-line intersection square. -/
theorem laurentConicComponentNormalized_isPullback :
    IsPullback (ProjectiveLine.overlapLeft K) (ProjectiveLine.overlapRight K)
      ((E).hom ≫ f) g := by
  apply (laurentConicComponentAffine_isPullback W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).of_iso'
    (Iso.refl _) E (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, ProjectiveLine.scaledOverlapLeft]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The two normalized full affine charts still exhaust the actual component. -/
theorem laurentConicComponentNormalized_cover (x : P) :
    (∃ y, ((E).hom ≫ f) y = x) ∨ ∃ z, g z = x := by
  rcases laurentConicComponentAffine_cover W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu x with
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
    (laurentConicComponentNormalized_isPullback W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)
    (laurentConicComponentNormalized_cover W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu)
local notation "J" => laurentConicComponentProjectiveIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

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
      laurentConicComponentFirstSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu := by
  rw [ProjectiveLine.zero, Category.assoc, laurentConicComponentProjectiveIso_left]
  change ProjectiveLine.chartZero K ≫ ProjectiveLine.chartScaling K ((hc).unit)⁻¹ ≫ f = _
  rw [ProjectiveLine.chartZero_chartScaling_assoc, laurentConicComponentFirstAffine_origin]

/-- Infinity is exactly the original second ordered attachment. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_infinity :
    ProjectiveLine.infinity K ≫ (J).hom =
      laurentConicComponentSecondSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu := by
  rw [ProjectiveLine.infinity, Category.assoc, laurentConicComponentProjectiveIso_right,
    laurentConicComponentSecondAffine_origin]

/-- The entire standard Laurent torus is the original terminal torus, without rescaling. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_torus :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ (J).hom = r := by
  rw [← Category.assoc, ProjectiveLine.overlap_condition, Category.assoc,
    laurentConicComponentProjectiveIso_right, laurentConicComponentSecondAffine_torus]

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
