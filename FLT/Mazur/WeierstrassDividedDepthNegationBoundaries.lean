/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthNegation
public import FLT.Mazur.WeierstrassSuccessiveNegationHorizontal

/-!
# Both actual attachment maps retain the constructed negatives

The preceding and next horizontal boundaries embed in the same incidence
chart. Their exact normalized maps are equivariant, providing both gluing
identities needed to extend negation through arbitrary retained exteriors.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))

omit [IsDomain R] in
/-- The normalized next-depth chart retains negation inside the entire local successor. -/
@[reassoc] theorem depthDividedChart_negation :
    (chartNegationIso e).hom ≫ depthDividedChart π k W e.b3 e.b4 e.b6 =
      depthDividedChart π k W e.b3 e.b4 e.b6 ≫
        modificationNegation W (π ^ k) π e.b3 e.b4 e.b6 := by
  change (WeierstrassDilatation.negationIso W (π ^ (k + 1)) e.b3 e.b4 e.b6).hom ≫
    (WeierstrassDilatation.parameterSpecIso W (π ^ k * π) (π ^ (k + 1))
      e.b3 e.b4 e.b6 e.b3 e.b4 e.b6 (pow_succ π k).symm rfl rfl rfl).hom ≫ _ = _
  rw [WeierstrassDilatation.negationIso_parameter_assoc]
  simp only [depthDividedChart, Category.assoc, dividedChart_modificationNegation]
  rfl

omit [IsDomain R] in
/-- The exact next boundary embedding is equivariant for the two actual negatives. -/
@[reassoc] theorem nextToX_negation :
    (boundaryNegationIso e).hom ≫ nextToX e = nextToX e ≫ (stepXNegationIso e).hom := by
  apply (cancel_mono (xChart W (π ^ k) π e.b3 e.b4 e.b6)).mp
  simp only [Category.assoc]
  change _ = nextToX e ≫ (negationIso W (π ^ k) π e.b3 e.b4 e.b6).hom ≫ _
  rw [← xChart_modificationNegation, nextToX_chart_assoc, nextToX_chart,
    boundaryNegationIso_inclusion_assoc, depthDividedChart_negation]

/-- The exact preceding boundary embedding retains its original divided negative. -/
@[reassoc] theorem previousToX_negation :
    (boundaryNegationIso d).hom ≫ previousToX hπ d e =
      previousToX hπ d e ≫ (stepXNegationIso e).hom := by
  let P := WeierstrassDilatation.horizontalNegationIso W (π ^ k)
    (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)
  have hp : P.hom ≫ (previousBoundaryIso hπ d e).hom =
      (previousBoundaryIso hπ d e).hom ≫ (boundaryNegationIso d).hom :=
    WeierstrassDilatation.horizontalNegationIso_parameter W (π ^ k) d.b3 d.b4 d.b6
      (π ^ k) (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
      (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
  apply (cancel_mono (xChart W (π ^ k) π e.b3 e.b4 e.b6)).mp
  apply (cancel_epi (previousBoundaryIso hπ d e).hom).mp
  simp only [Category.assoc]
  rw [← Category.assoc (previousBoundaryIso hπ d e).hom, ← hp]
  simp only [previousToX, Category.assoc, Iso.hom_inv_id_assoc]
  change P.hom ≫ previousHorizontalChart W (π ^ k) π e.b3 e.b4 e.b6 = _
  rw [previousHorizontalChart_negation]
  simp only [previousHorizontalChart, Category.assoc, xChart_modificationNegation]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
