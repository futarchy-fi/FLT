/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXContractionOverlap
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Gluing the actual local modification charts

The x-direction and divided charts are glued on their proved principal-open
overlap. Their contractions descend to the original cubic. This construction
does not yet identify the resulting scheme with the saturated blowup.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassModificationX

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The common overlap, mapped into the divided chart. -/
def overlapToDivided : Spec (.of (XOpen W s b3 b4 b6)) ⟶
    Spec (.of (WeierstrassDilatation.Coordinate W s b3 b4 b6)) :=
  (overlapIso W s b3 b4 b6).hom ≫ dividedOpenInclusion W s b3 b4 b6

instance overlapToDivided_isOpenImmersion :
    IsOpenImmersion (overlapToDivided W s b3 b4 b6) := by
  dsimp [overlapToDivided]
  infer_instance

/-- The scheme obtained by gluing the two actual equation charts. -/
def modification : Scheme :=
  pushout (xOpenInclusion W s b3 b4 b6) (overlapToDivided W s b3 b4 b6)

/-- The x-direction chart of the glued modification. -/
def xChart : Spec (.of (Coordinate W s b3 b4 b6)) ⟶ modification W s b3 b4 b6 :=
  pushout.inl _ _

/-- The divided chart of the glued modification. -/
def dividedChart : Spec (.of (WeierstrassDilatation.Coordinate W s b3 b4 b6)) ⟶
    modification W s b3 b4 b6 := pushout.inr _ _

instance xChart_isOpenImmersion : IsOpenImmersion (xChart W s b3 b4 b6) := by
  change IsOpenImmersion (colimit.ι
    (span (xOpenInclusion W s b3 b4 b6) (overlapToDivided W s b3 b4 b6)) WalkingSpan.left)
  infer_instance

instance dividedChart_isOpenImmersion : IsOpenImmersion (dividedChart W s b3 b4 b6) := by
  change IsOpenImmersion (colimit.ι
    (span (xOpenInclusion W s b3 b4 b6) (overlapToDivided W s b3 b4 b6)) WalkingSpan.right)
  infer_instance

/-- The chart inclusions identify exactly the prescribed overlap maps. -/
theorem chart_overlap : xOpenInclusion W s b3 b4 b6 ≫ xChart W s b3 b4 b6 =
    overlapToDivided W s b3 b4 b6 ≫ dividedChart W s b3 b4 b6 := pushout.condition

/-- Every point of the glued scheme belongs to one of the two constructed charts. -/
theorem modification_charts_cover (z : modification W s b3 b4 b6) :
    (∃ a, xChart W s b3 b4 b6 a = z) ∨ ∃ a, dividedChart W s b3 b4 b6 a = z := by
  obtain ⟨i, a, ha⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (xOpenInclusion W s b3 b4 b6) (overlapToDivided W s b3 b4 b6)) z
  cases i with
  | none =>
    left
    refine ⟨xOpenInclusion W s b3 b4 b6 a, ?_⟩
    change (xOpenInclusion W s b3 b4 b6 ≫ xChart W s b3 b4 b6) a = z
    rw [show xOpenInclusion W s b3 b4 b6 ≫ xChart W s b3 b4 b6 =
      colimit.ι (span (xOpenInclusion W s b3 b4 b6) (overlapToDivided W s b3 b4 b6))
        WalkingSpan.zero from colimit.w
          (span (xOpenInclusion W s b3 b4 b6) (overlapToDivided W s b3 b4 b6))
          WalkingSpan.Hom.fst]
    exact ha
  | some i =>
    cases i with
    | left => exact Or.inl ⟨a, ha⟩
    | right => exact Or.inr ⟨a, ha⟩

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The actual contractions descend to a morphism from the glued modification. -/
def contraction : modification W s b3 b4 b6 ⟶
    WeierstrassIntegralChart.integralCurve W :=
  pushout.desc (toCurve W s b3 b4 b6 h3 h4 h6)
    (WeierstrassDilatation.toCurve W s b3 b4 b6 h3 h4 h6)
    (by simpa only [overlapToDivided, Category.assoc] using
      (overlapIso_toCurve W s b3 b4 b6 h3 h4 h6).symm)

/-- The descended map is the original contraction on the x-direction chart. -/
@[reassoc (attr := simp)] theorem xChart_contraction :
    xChart W s b3 b4 b6 ≫ contraction W s b3 b4 b6 h3 h4 h6 =
      toCurve W s b3 b4 b6 h3 h4 h6 := pushout.inl_desc _ _ _

/-- The descended map is the original contraction on the divided chart. -/
@[reassoc (attr := simp)] theorem dividedChart_contraction :
    dividedChart W s b3 b4 b6 ≫ contraction W s b3 b4 b6 h3 h4 h6 =
      WeierstrassDilatation.toCurve W s b3 b4 b6 h3 h4 h6 := pushout.inr_desc _ _ _

end FLT.Mazur.WeierstrassModificationX
