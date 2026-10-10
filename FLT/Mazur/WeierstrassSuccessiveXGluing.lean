/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXSchemeOverlap
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Gluing one successive modification of an actual divided chart

The new three-generator x-direction chart and the deeper divided chart glue
along their proved principal-open equivalence. Both are open subschemes of
the constructed scheme, cover it, and retain their actual contractions.
This constructs a local step; global iteration and properness are separate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassSuccessiveX

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The common overlap, mapped into the divided chart. -/
def overlapToDivided : Spec (.of (XOpen W s π b3 b4 b6)) ⟶
    Spec (.of (WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6)) :=
  (overlapIso W s π b3 b4 b6).hom ≫ dividedOpenInclusion W s π b3 b4 b6

instance overlapToDivided_isOpenImmersion :
    IsOpenImmersion (overlapToDivided W s π b3 b4 b6) := by
  dsimp [overlapToDivided]
  infer_instance

/-- The scheme obtained by gluing the two actual equation charts. -/
def modification : Scheme :=
  pushout (xOpenInclusion W s π b3 b4 b6) (overlapToDivided W s π b3 b4 b6)

/-- The x-direction chart of the glued modification. -/
def xChart : Spec (.of (Coordinate W s π b3 b4 b6)) ⟶ modification W s π b3 b4 b6 :=
  pushout.inl _ _

/-- The divided chart of the glued modification. -/
def dividedChart : Spec (.of (WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6)) ⟶
    modification W s π b3 b4 b6 := pushout.inr _ _

instance xChart_isOpenImmersion : IsOpenImmersion (xChart W s π b3 b4 b6) := by
  change IsOpenImmersion (colimit.ι
    (span (xOpenInclusion W s π b3 b4 b6) (overlapToDivided W s π b3 b4 b6)) WalkingSpan.left)
  infer_instance

instance dividedChart_isOpenImmersion : IsOpenImmersion (dividedChart W s π b3 b4 b6) := by
  change IsOpenImmersion (colimit.ι
    (span (xOpenInclusion W s π b3 b4 b6) (overlapToDivided W s π b3 b4 b6)) WalkingSpan.right)
  infer_instance

/-- The chart inclusions identify exactly the prescribed overlap maps. -/
theorem chart_overlap : xOpenInclusion W s π b3 b4 b6 ≫ xChart W s π b3 b4 b6 =
    overlapToDivided W s π b3 b4 b6 ≫ dividedChart W s π b3 b4 b6 := pushout.condition

/-- Every point of the glued scheme belongs to one of the two constructed charts. -/
theorem modification_charts_cover (z : modification W s π b3 b4 b6) :
    (∃ a, xChart W s π b3 b4 b6 a = z) ∨ ∃ a, dividedChart W s π b3 b4 b6 a = z := by
  obtain ⟨i, a, ha⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (xOpenInclusion W s π b3 b4 b6) (overlapToDivided W s π b3 b4 b6)) z
  cases i with
  | none =>
    left
    refine ⟨xOpenInclusion W s π b3 b4 b6 a, ?_⟩
    change (xOpenInclusion W s π b3 b4 b6 ≫ xChart W s π b3 b4 b6) a = z
    rw [show xOpenInclusion W s π b3 b4 b6 ≫ xChart W s π b3 b4 b6 =
      colimit.ι (span (xOpenInclusion W s π b3 b4 b6) (overlapToDivided W s π b3 b4 b6))
        WalkingSpan.zero from colimit.w
          (span (xOpenInclusion W s π b3 b4 b6) (overlapToDivided W s π b3 b4 b6))
          WalkingSpan.Hom.fst]
    exact ha
  | some i =>
    cases i with
    | left => exact Or.inl ⟨a, ha⟩
    | right => exact Or.inr ⟨a, ha⟩

/-- The actual chart contractions descend to the preceding divided chart. -/
def contraction : modification W s π b3 b4 b6 ⟶
    Spec (.of (WeierstrassDilatation.Coordinate W s
      (π * b3) (π * b4) (π ^ 2 * b6))) :=
  pushout.desc (toDivided W s π b3 b4 b6) (dividedToPrevious W s π b3 b4 b6)
    (by simpa only [overlapToDivided, Category.assoc] using
      (overlapIso_toPrevious W s π b3 b4 b6).symm)

/-- The descended map retains the actual successive x-direction contraction. -/
@[reassoc (attr := simp)] theorem xChart_contraction :
    xChart W s π b3 b4 b6 ≫ contraction W s π b3 b4 b6 =
      toDivided W s π b3 b4 b6 := pushout.inl_desc _ _ _

/-- The descended map retains the actual deeper divided contraction. -/
@[reassoc (attr := simp)] theorem dividedChart_contraction :
    dividedChart W s π b3 b4 b6 ≫ contraction W s π b3 b4 b6 =
      dividedToPrevious W s π b3 b4 b6 := pushout.inr_desc _ _ _

/-- The successive modification retains the original projective cubic contraction. -/
def contractionToCurve (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
    (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6)) :
    modification W s π b3 b4 b6 ⟶ WeierstrassIntegralChart.integralCurve W :=
  contraction W s π b3 b4 b6 ≫
    WeierstrassDilatation.toCurve W s (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6

end FLT.Mazur.WeierstrassSuccessiveX
