/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData
public import FLT.Mazur.WeierstrassSuccessiveXHorizontalScheme

/-!
# The two actual boundaries of a successive depth chart

The preceding horizontal boundary and the deeper horizontal boundary both
embed in the new x-direction chart. The embeddings retain their contractions
and identify the actual next divided chart along its principal open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
open WeierstrassSuccessiveX

/-- The actual successive x-direction chart at depth k. -/
def stepX : Scheme := Spec (.of (Coordinate W (π ^ k) π e.b3 e.b4 e.b6))

/-- Identification of the preceding normalized horizontal boundary. -/
def previousBoundaryIso :
    Spec (.of (PreviousHorizontalOpen W (π ^ k) π e.b3 e.b4 e.b6)) ≅ boundary d :=
  WeierstrassDilatation.horizontalParameterIso W (π ^ k) (π ^ k) d.b3 d.b4 d.b6
    (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
    (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)

/-- Identification of the deeper normalized horizontal boundary. -/
def nextBoundaryIso : boundary e ≅
    Spec (.of (DividedOpen W (π ^ k) π e.b3 e.b4 e.b6)) :=
  WeierstrassDilatation.horizontalParameterIso W (π ^ k * π) (π ^ (k + 1))
    e.b3 e.b4 e.b6 e.b3 e.b4 e.b6 (pow_succ π k).symm rfl rfl rfl

/-- The preceding horizontal boundary embeds in the new x-direction chart. -/
def previousToX : boundary d ⟶ stepX e :=
  (previousBoundaryIso hπ d e).inv ≫
    (horizontalIso W (π ^ k) π e.b3 e.b4 e.b6).inv ≫
      horizontalOpenInclusion W (π ^ k) π e.b3 e.b4 e.b6

/-- The deeper horizontal boundary embeds in the same new x-direction chart. -/
def nextToX : boundary e ⟶ stepX e :=
  (nextBoundaryIso e).hom ≫ (overlapIso W (π ^ k) π e.b3 e.b4 e.b6).inv ≫
    xOpenInclusion W (π ^ k) π e.b3 e.b4 e.b6

instance previousToX_isOpenImmersion : IsOpenImmersion (previousToX hπ d e) := by
  unfold previousToX
  infer_instance

instance nextToX_isOpenImmersion : IsOpenImmersion (nextToX e) := by
  unfold nextToX
  infer_instance

/-- The actual x-direction contraction to the normalized preceding divided chart. -/
def xContraction : stepX e ⟶ chart d :=
  toDivided W (π ^ k) π e.b3 e.b4 e.b6 ≫
    (WeierstrassDilatation.parameterSpecIso W (π ^ k) (π ^ k) d.b3 d.b4 d.b6
      (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
      (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)).hom

/-- The preceding boundary is unchanged by the actual contraction. -/
@[reassoc] theorem previousToX_contraction :
    previousToX hπ d e ≫ xContraction hπ d e = boundaryInclusion d := by
  simp only [previousToX, xContraction, Category.assoc,
    ← horizontalIso_toDivided_assoc, Iso.inv_hom_id_assoc]
  change (previousBoundaryIso hπ d e).inv ≫
    WeierstrassDilatation.horizontalInclusion W (π ^ k)
      (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) ≫ _ =
    WeierstrassDilatation.horizontalInclusion W (π ^ k) d.b3 d.b4 d.b6
  rw [← WeierstrassDilatation.horizontalParameterIso_inclusion]
  exact (previousBoundaryIso hπ d e).inv_hom_id_assoc _

omit [IsDomain R] in
/-- The next boundary agrees with the actual deeper chart inside the local modification. -/
@[reassoc] theorem nextToX_chart :
    nextToX e ≫ xChart W (π ^ k) π e.b3 e.b4 e.b6 =
      boundaryInclusion e ≫ depthDividedChart π k W e.b3 e.b4 e.b6 := by
  have h := chart_overlap W (π ^ k) π e.b3 e.b4 e.b6
  simp only [overlapToDivided, Category.assoc] at h
  simp only [nextToX, Category.assoc, h, Iso.inv_hom_id_assoc]
  exact WeierstrassDilatation.horizontalParameterIso_inclusion_assoc W (π ^ k * π) (π ^ (k + 1))
    e.b3 e.b4 e.b6 e.b3 e.b4 e.b6 (pow_succ π k).symm rfl rfl rfl _

/-- The next boundary contracts by the actual depth transition. -/
@[reassoc] theorem nextToX_contraction :
    nextToX e ≫ xContraction hπ d e = boundaryInclusion e ≫ transition hπ d e := by
  have hx : xContraction hπ d e = xChart W (π ^ k) π e.b3 e.b4 e.b6 ≫
      depthContraction π k hπ W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
        d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6 := by
    simp only [depthContraction, xChart_contraction_assoc]
    rfl
  rw [hx, ← Category.assoc, nextToX_chart, Category.assoc,
    depthDividedChart_contraction]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
