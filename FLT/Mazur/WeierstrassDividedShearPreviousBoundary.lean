/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShearHorizontal
public import FLT.Mazur.WeierstrassSuccessiveXShearHorizontal
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra
public import FLT.Mazur.WeierstrassDividedShearContraction

/-!
# Shearing the original parameter-corrected previous boundary

The actual full previous-boundary equivalence commutes with shear. This
retains the preceding attachment used in exterior iteration, not just its
contraction to the original cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1)) (r : R)
local notation "U" => rootShearCurve W r
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ k) (π ^ k)
  d.b3 d.b4 d.b6 (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
local notation "p'" => WeierstrassDilatation.parameterEquiv U (π ^ k) (π ^ k)
  d.b3 (d.b4 - r * d.b3) d.b6 (π * e.b3) (π * (e.b4 - r * e.b3)) (π ^ 2 * e.b6) rfl
  (factor3_step hπ (shearData d r) (shearData e r))
  (factor4_step hπ (shearData d r) (shearData e r))
  (factor6_step hπ (shearData d r) (shearData e r))
local notation "f" => WeierstrassSuccessiveX.fromDivided W (π ^ k) π e.b3 e.b4 e.b6
local notation "f'" => WeierstrassSuccessiveX.fromDivided U (π ^ k) π
  e.b3 (e.b4 - r * e.b3) e.b6
local notation "a" => WeierstrassDilatation.horizontalShearEquiv W (π ^ k) d.b3 d.b4 d.b6 r
local notation "b" => WeierstrassSuccessiveX.horizontalShearEquiv W (π ^ k) π e.b3 e.b4 e.b6 r

/-- Shearing commutes with the full parameter-corrected incidence contraction. -/
theorem shear_previousContraction :
    (WeierstrassSuccessiveX.shearForward W (π ^ k) π e.b3 e.b4 e.b6 r).comp
        ((f).comp (p).toAlgHom) =
      ((f').comp (p').toAlgHom).comp
        (WeierstrassDilatation.shearForward W (π ^ k) d.b3 d.b4 d.b6 r) := by
  apply WeierstrassDilatation.hom_ext
  · simp
  · simp [mul_add, mul_comm]

/-- The complete preceding boundary equivalence retains all original functions under shear. -/
theorem shear_previousBoundaryEquiv :
    (b).toAlgHom.comp (previousBoundaryEquiv hπ d e).toAlgHom =
      (previousBoundaryEquiv hπ (shearData d r) (shearData e r)).toAlgHom.comp (a).toAlgHom := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6))
  apply AlgHom.ext
  intro z
  change b (previousBoundaryEquiv hπ d e (algebraMap _ _ z)) =
    previousBoundaryEquiv hπ (shearData d r) (shearData e r) (a (algebraMap _ _ z))
  rw [previousBoundaryEquiv_base, WeierstrassSuccessiveX.horizontalShearEquiv_base,
    WeierstrassDilatation.horizontalShearEquiv_base]
  erw [previousBoundaryEquiv_base]
  exact congrArg (algebraMap _ _) (AlgHom.congr_fun (shear_previousContraction hπ d e r) z)

/-- The actual divided boundary scheme shear at a named depth. -/
def shearBoundaryIso : boundary (shearData d r) ≅ boundary d :=
  WeierstrassDilatation.horizontalShearIso W (π ^ k) d.b3 d.b4 d.b6 r

omit [IsDomain R] in
/-- The boundary shear retains the original divided open immersion. -/
@[reassoc] theorem shearBoundaryIso_inclusion :
    (shearBoundaryIso d r).hom ≫ boundaryInclusion d =
      boundaryInclusion (shearData d r) ≫ (shearChartIso d r).hom :=
  WeierstrassDilatation.horizontalShearIso_inclusion W (π ^ k) d.b3 d.b4 d.b6 r

/-- The original successive chart isomorphism at the named next depth. -/
def shearStepXIso : stepX (shearData e r) ≅ stepX e :=
  Scheme.Spec.mapIso (WeierstrassSuccessiveX.shearEquiv W (π ^ k) π e.b3 e.b4 e.b6 r
    ).toRingEquiv.toCommRingCatIso.op

/-- The actual successive contraction commutes after retaining its parameter equivalence. -/
@[reassoc] theorem shearStepXIso_contraction :
    (shearStepXIso e r).hom ≫ xContraction hπ d e =
      xContraction hπ (shearData d r) (shearData e r) ≫ (shearChartIso d r).hom := by
  change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) =
    (Spec.map _ ≫ Spec.map _) ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g.toRingHom))
    (shear_previousContraction hπ d e r)

/-- The original previous-boundary attachment itself commutes with shear. -/
@[reassoc] theorem shearStepXIso_previousToX :
    previousToX hπ (shearData d r) (shearData e r) ≫ (shearStepXIso e r).hom =
      (shearBoundaryIso d r).hom ≫ previousToX hπ d e := by
  let q := Scheme.Spec.mapIso
    (previousBoundaryEquiv hπ (shearData d r) (shearData e r)
      ).toRingEquiv.toCommRingCatIso.op
  apply (cancel_epi q.hom).mp
  have h : q.hom ≫ (shearBoundaryIso d r).hom =
      Spec.map (CommRingCat.ofHom (b).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (previousBoundaryEquiv hπ d e).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun g => Spec.map (CommRingCat.ofHom g.toRingHom))
      (shear_previousBoundaryEquiv hπ d e r).symm
  rw [← Category.assoc, show q.hom ≫ previousToX hπ (shearData d r) (shearData e r) =
      WeierstrassSuccessiveX.horizontalOpenInclusion U (π ^ k) π
        e.b3 (e.b4 - r * e.b3) e.b6 from
    previousBoundaryEquiv_previousToX hπ (shearData d r) (shearData e r)]
  rw [← Category.assoc, h, Category.assoc,
    previousBoundaryEquiv_previousToX hπ d e]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (WeierstrassSuccessiveX.horizontalShearEquiv_base W (π ^ k) π e.b3 e.b4 e.b6 r z
    ).symm

end FLT.Mazur.WeierstrassDividedDepth
