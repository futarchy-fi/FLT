/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearContraction
public import FLT.Mazur.WeierstrassModificationShearLocalization
public import FLT.Mazur.WeierstrassModificationGluing

/-!
# The shear on the whole original two-chart modification

Glue the constructed isomorphisms along the actual reciprocal overlap.
The resulting whole-model isomorphism retains both original charts and
its contraction to the integral cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (d : Data W π k) (r : R)
local notation "U" => rootShearCurve W r
local notation "e" => shearData d r
local notation "B" => XOpen W (π ^ k) d.b3 d.b4 d.b6
local notation "B'" => XOpen U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6
local notation "i" => xOpenInclusion W (π ^ k) d.b3 d.b4 d.b6
local notation "i'" => xOpenInclusion U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6
local notation "j" => overlapToDivided W (π ^ k) d.b3 d.b4 d.b6
local notation "j'" => overlapToDivided U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6

/-- The actual overlap isomorphism induced by the incidence shear. -/
def shearOverlapIso : Spec (.of B') ≅ Spec (.of B) :=
  Scheme.Spec.mapIso (xOpenShearEquiv W (π ^ k) d.b3 d.b4 d.b6 r
    ).toRingEquiv.toCommRingCatIso.op

/-- The localized isomorphism retains the original incidence inclusion. -/
@[reassoc] theorem shearOverlapIso_incidence :
    i' ≫ (shearIncidenceIso d r).hom = (shearOverlapIso d r).hom ≫ i := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (xOpenShearEquiv_base W (π ^ k) d.b3 d.b4 d.b6 r z).symm

/-- The existing reciprocal attachment is the spectrum of its complete algebra map. -/
theorem shear_overlapToDivided_spec (V : WeierstrassCurve R) (s b3 b4 b6 : R) :
    overlapToDivided V s b3 b4 b6 =
      Spec.map (CommRingCat.ofHom (dividedToXOpen V s b3 b4 b6).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact overlapForward_base V s b3 b4 b6 z

/-- The same overlap isomorphism retains the entire divided-chart attachment. -/
@[reassoc] theorem shearOverlapIso_divided :
    j' ≫ (shearChartIso d r).hom = (shearOverlapIso d r).hom ≫ j := by
  rw [shear_overlapToDivided_spec, shear_overlapToDivided_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (xOpenShearEquiv_dividedToXOpen W (π ^ k) d.b3 d.b4 d.b6 r).symm

/-- The whole original local modification is preserved by the actual integral shear. -/
def shearModificationIso :
    modification U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 ≅
      modification W (π ^ k) d.b3 d.b4 d.b6 :=
  asIso (pushout.map i' j' i j (shearIncidenceIso d r).hom (shearChartIso d r).hom
    (shearOverlapIso d r).hom (shearOverlapIso_incidence d r) (shearOverlapIso_divided d r))

/-- The whole comparison retains the complete original incidence chart. -/
@[reassoc] theorem shearModificationIso_incidence :
    xChart U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 ≫ (shearModificationIso d r).hom =
      (shearIncidenceIso d r).hom ≫ xChart W (π ^ k) d.b3 d.b4 d.b6 := by
  simp [shearModificationIso, xChart]

/-- The whole comparison retains the complete original divided chart. -/
@[reassoc] theorem shearModificationIso_divided :
    dividedChart U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 ≫ (shearModificationIso d r).hom =
      (shearChartIso d r).hom ≫ dividedChart W (π ^ k) d.b3 d.b4 d.b6 := by
  simp [shearModificationIso, dividedChart]

/-- The glued comparison retains the actual integral variable-change cubic projection. -/
@[reassoc] theorem shearModificationIso_contraction :
    (shearModificationIso d r).hom ≫ contraction W (π ^ k) d.b3 d.b4 d.b6
        d.factor3 d.factor4 d.factor6 =
      contraction U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6
        (e).factor3 (e).factor4 (e).factor6 ≫
        (integralVariableChangeIso W U (⟨1, 0, r, 0⟩) rfl).hom := by
  apply pushout.hom_ext
  · change xChart U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 ≫ _ =
      xChart U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 ≫ _
    rw [shearModificationIso_incidence_assoc, xChart_contraction,
      xChart_contraction_assoc]
    exact shearIncidenceIso_toCurve d r
  · change dividedChart U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 ≫ _ =
      dividedChart U (π ^ k) d.b3 (d.b4 - r * d.b3) d.b6 ≫ _
    rw [shearModificationIso_divided_assoc, dividedChart_contraction,
      dividedChart_contraction_assoc]
    exact shearChartIso_toCurve d r

end FLT.Mazur.WeierstrassDividedDepth
