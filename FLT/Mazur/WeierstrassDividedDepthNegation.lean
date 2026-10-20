/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationNegationBoundary
public import FLT.Mazur.WeierstrassSuccessiveXNegationContraction
public import FLT.Mazur.WeierstrassDividedDepthBoundary

/-!
# Negation on the actual normalized divided-depth data

Use the original coefficient factorizations to retain each actual depth
transition and the actual incidence contraction. Boundary involutions are
constructed on the original localized algebras, not on replacement models.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}

/-- The constructed negative of the actual equation chart at a named depth. -/
def chartNegationIso (d : Data W π k) : chart d ≅ chart d :=
  WeierstrassDilatation.negationIso W (π ^ k) d.b3 d.b4 d.b6

/-- The constructed negative of its entire horizontal boundary. -/
def boundaryNegationIso (d : Data W π k) : boundary d ≅ boundary d :=
  WeierstrassDilatation.horizontalNegationIso W (π ^ k) d.b3 d.b4 d.b6

/-- The negative on the whole actual three-generator chart at the next step. -/
def stepXNegationIso (e : Data W π (k + 1)) : stepX e ≅ stepX e :=
  WeierstrassSuccessiveX.negationIso W (π ^ k) π e.b3 e.b4 e.b6

/-- The normalized boundary inclusion retains the constructed negative. -/
@[reassoc] theorem boundaryNegationIso_inclusion (d : Data W π k) :
    (boundaryNegationIso d).hom ≫ boundaryInclusion d =
      boundaryInclusion d ≫ (chartNegationIso d).hom :=
  WeierstrassDilatation.horizontalNegationIso_inclusion W (π ^ k) d.b3 d.b4 d.b6

/-- Every actual divided-depth chart keeps the original cubic inverse. -/
@[reassoc] theorem chartNegationIso_toCurve (d : Data W π k) :
    (chartNegationIso d).hom ≫ toCurve d =
      toCurve d ≫ WeierstrassIntegralChart.integralCurveNegation W :=
  WeierstrassDilatation.negationIso_toCurve W (π ^ k) d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6

variable [IsDomain R] (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))

/-- Negation commutes with the exact existing normalized depth transition. -/
@[reassoc] theorem chartNegationIso_transition :
    (chartNegationIso e).hom ≫ transition hπ d e =
      transition hπ d e ≫ (chartNegationIso d).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun f :
    WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R]
      WeierstrassDilatation.Coordinate W (π ^ (k + 1)) e.b3 e.b4 e.b6 =>
        CommRingCat.ofHom f.toRingHom)
    (WeierstrassDilatation.negation_depthTransition W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
      π k (k + 1) hπ (Nat.le_succ k) d.factor3 d.factor4 d.factor6
      e.factor3 e.factor4 e.factor6))

/-- The whole incidence chart negative retains the normalized preceding equation map. -/
@[reassoc] theorem stepXNegationIso_contraction :
    (stepXNegationIso e).hom ≫ xContraction hπ d e =
      xContraction hπ d e ≫ (chartNegationIso d).hom := by
  let q := WeierstrassDilatation.parameterSpecIso W (π ^ k) (π ^ k) d.b3 d.b4 d.b6
    (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
    (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
  let c := WeierstrassSuccessiveX.toDivided W (π ^ k) π e.b3 e.b4 e.b6
  let a := WeierstrassDilatation.negationIso W (π ^ k)
    (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)
  have hc : (stepXNegationIso e).hom ≫ c = c ≫ a.hom :=
    WeierstrassSuccessiveX.negationIso_toDivided W (π ^ k) π e.b3 e.b4 e.b6
  have hq : a.hom ≫ q.hom = q.hom ≫ (chartNegationIso d).hom :=
    WeierstrassDilatation.negationIso_parameter W (π ^ k) d.b3 d.b4 d.b6
      (π ^ k) (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
      (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
  change (stepXNegationIso e).hom ≫ (c ≫ q.hom) =
    (c ≫ q.hom) ≫ (chartNegationIso d).hom
  calc
    _ = ((stepXNegationIso e).hom ≫ c) ≫ q.hom := (Category.assoc _ _ _).symm
    _ = (c ≫ a.hom) ≫ q.hom := congrArg (· ≫ q.hom) hc
    _ = c ≫ (a.hom ≫ q.hom) := Category.assoc _ _ _
    _ = c ≫ (q.hom ≫ (chartNegationIso d).hom) := congrArg (c ≫ ·) hq
    _ = _ := (Category.assoc _ _ _).symm

end FLT.Mazur.WeierstrassDividedDepth
