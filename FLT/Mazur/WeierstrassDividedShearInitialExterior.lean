/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearExterior
public import FLT.Mazur.WeierstrassDividedShearGluing
public import FLT.Mazur.WeierstrassDividedInitialExterior

/-!
# The actual initial exterior satisfies the shear attachment square

Use the original two-chart modification to retain the full original
initial attachment. This supplies the concrete base case for finite iteration.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (d : Data W π k) (r : R)
local notation "U" => rootShearCurve W r
local notation "e" => shearData d r

/-- The original initial attachment retains the original two-chart overlap square. -/
@[reassoc] theorem initialExterior_attach_chart :
    (initialExterior d).attach ≫ WeierstrassModificationX.xChart W (π ^ k) d.b3 d.b4 d.b6 =
      boundaryInclusion d ≫
        WeierstrassModificationX.dividedChart W (π ^ k) d.b3 d.b4 d.b6 := by
  have h := congrArg (fun g => g ≫ (initialExteriorIso d).hom) (initialExterior d).overlap
  simpa only [Category.assoc, initialExteriorIso_exterior, initialExteriorIso_divided] using h

/-- The actual whole incidence shear compares the two original initial exteriors. -/
def shearInitialExteriorIso : (initialExterior e).carrier ≅ (initialExterior d).carrier :=
  shearIncidenceIso d r

/-- The original initial attachment commutes with the actual shear on its whole domain. -/
@[reassoc] theorem shearInitialExteriorIso_attach :
    (initialExterior e).attach ≫ (shearInitialExteriorIso d r).hom =
      (shearBoundaryIso d r).hom ≫ (initialExterior d).attach := by
  apply (cancel_mono (WeierstrassModificationX.xChart W (π ^ k) d.b3 d.b4 d.b6)).mp
  have hx : (shearInitialExteriorIso d r).hom ≫
      WeierstrassModificationX.xChart W (π ^ k) d.b3 d.b4 d.b6 =
      WeierstrassModificationX.xChart U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 ≫
        (shearModificationIso d r).hom := (shearModificationIso_incidence d r).symm
  rw [Category.assoc, hx, ← Category.assoc]
  erw [initialExterior_attach_chart (shearData d r)]
  erw [Category.assoc, shearModificationIso_divided d r, ← Category.assoc,
    ← shearBoundaryIso_inclusion d r, Category.assoc, ← initialExterior_attach_chart d,
    Category.assoc]
  simp only [initialExterior, Category.assoc]

/-- The whole initial exterior construction is identified with its actual shear. -/
def shearInitialWholeIso : (initialExterior e).whole ≅ (initialExterior d).whole :=
  shearWholeIso r (initialExterior d) (initialExterior e) (shearInitialExteriorIso d r)
    (shearInitialExteriorIso_attach d r)

/-- The initial whole comparison retains the original integral cubic variable change. -/
@[reassoc] theorem shearInitialWholeIso_toCurve :
    (shearInitialWholeIso d r).hom ≫ initialToCurve d =
      initialToCurve e ≫
        (WeierstrassIntegralChart.integralVariableChangeIso W U (⟨1, 0, r, 0⟩) rfl).hom := by
  apply Exterior.hom_ext
  · rw [show (shearInitialWholeIso d r).hom =
        (shearWholeIso r (initialExterior d) (initialExterior e) (shearInitialExteriorIso d r)
          (shearInitialExteriorIso_attach d r)).hom from rfl]
    rw [shearWholeIso_exterior_assoc, initialToCurve_exterior, initialToCurve_exterior_assoc]
    exact shearIncidenceIso_toCurve d r
  · rw [show (shearInitialWholeIso d r).hom =
        (shearWholeIso r (initialExterior d) (initialExterior e) (shearInitialExteriorIso d r)
          (shearInitialExteriorIso_attach d r)).hom from rfl]
    rw [shearWholeIso_divided_assoc, initialToCurve_divided, initialToCurve_divided_assoc]
    exact shearChartIso_toCurve d r

end FLT.Mazur.WeierstrassDividedDepth
