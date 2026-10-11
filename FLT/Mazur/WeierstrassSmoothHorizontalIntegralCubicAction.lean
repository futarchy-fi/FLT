/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalIntegralActionSource
public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# The original cubic action on the named integral source

The original horizontal input and genuine output contract to the same
secant addition square before any residue specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : WeierstrassDividedDepth.Data W π k)
local notation "S" => SmoothHorizontalProductRing W (π ^ k)
local notation "a" => smoothHorizontalLeft W (π ^ k)
local notation "c" => smoothHorizontalRight W (π ^ k)
local notation "p" => smoothHorizontalPoint W (π ^ k)
local notation "T" => SecantPairRing W a c
local notation "O" => SmoothHorizontalActionRing d
local notation "H" => HorizontalSourceRing W (π ^ k)
local notation "α" => AlgHom.comp (secantPairPresentation W a c)
  (ordinaryChartAddition W false)

instance smoothHorizontalActionRingCoefficientSecantTower : IsScalarTower R T O := by
  unfold SmoothHorizontalActionRing
  infer_instance

/-- The retained smooth parameter on the actual integral action source. -/
def smoothHorizontalIntegralPoint : Spec (.of O) ⟶ (integralSmoothOpen W).toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap S O)) ≫ p

/-- The original affine cubic input on the integral action source. -/
def smoothHorizontalIntegralCubicInput : Coordinate W 2 →ₐ[R] O :=
  (smoothHorizontalIntegralInput d).comp (IsScalarTower.toAlgHom R (Coordinate W 2) H)

/-- The original affine cubic output of the genuine horizontal lift. -/
def smoothHorizontalIntegralCubicOutput : Coordinate W 2 →ₐ[R] O :=
  (smoothHorizontalIntegralOutput d).comp (IsScalarTower.toAlgHom R (Coordinate W 2) H)

/-- The integral input is the original right product projection on every cubic function. -/
theorem smoothHorizontalIntegralCubicInput_eq :
    smoothHorizontalIntegralCubicInput d = (IsScalarTower.toAlgHom R S O).comp c := rfl

/-- The genuine output retains the actual secant addition on every cubic function. -/
theorem smoothHorizontalIntegralCubicOutput_eq :
    smoothHorizontalIntegralCubicOutput d = (IsScalarTower.toAlgHom R T O).comp α := by
  apply AlgHom.ext
  intro q
  exact secantHorizontalActionLift_base W π d.b3 d.b4 (π ^ k * d.b6)
    d.factor3 d.factor4 (smoothHorizontal_factor6 d) a c p
    (smoothHorizontalLeft_inclusion W (π ^ k)) (smoothHorizontal_structure W (π ^ k))
    (smoothHorizontalInput W (π ^ k)) (smoothHorizontalRight_contraction W (π ^ k))
    (smoothHorizontalInput_flat W (π ^ k)) q

/-- The retained smooth point and cubic input have the same original coefficient point. -/
theorem smoothHorizontalIntegralPoint_condition :
    smoothHorizontalIntegralPoint d ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom (smoothHorizontalIntegralCubicInput d).toRingHom) ≫
        integralCurveChart W 2) ≫ integralCurveStructure W := by
  rw [smoothHorizontalIntegralPoint, Category.assoc, smoothHorizontal_structure,
    smoothHorizontalIntegralCubicInput_eq]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc]
  rfl

/-- The smooth point retains the original coefficient map of the integral action source. -/
@[reassoc] theorem smoothHorizontalIntegralPoint_structure :
    smoothHorizontalIntegralPoint d ≫ integralSmoothStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [smoothHorizontalIntegralPoint_condition, Category.assoc, integralCurveChart_structure]
  exact specAlgHom_structure (smoothHorizontalIntegralCubicInput d)

/-- The actual integral output contracts to genuine addition on the original cubic. -/
theorem smoothHorizontalIntegralCubicOutput_addition :
    Spec.map (CommRingCat.ofHom (smoothHorizontalIntegralCubicOutput d).toRingHom) ≫
        integralCurveChart W 2 =
      leftSmoothPointAddition W (smoothHorizontalIntegralPoint d)
        (Spec.map (CommRingCat.ofHom (smoothHorizontalIntegralCubicInput d).toRingHom) ≫
          integralCurveChart W 2) (smoothHorizontalIntegralPoint_condition d) := by
  have h := congrArg (Spec.map (CommRingCat.ofHom (algebraMap T O)) ≫ ·)
    (secantPairSmooth_addition W a c p (smoothHorizontalLeft_inclusion W (π ^ k))
      (smoothHorizontal_structure W (π ^ k)))
  rw [← leftSmoothPointAddition_comp] at h
  simp only [smoothHorizontalIntegralCubicOutput_eq, smoothHorizontalIntegralCubicInput_eq]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc] at h ⊢
  have hq : Spec.map (CommRingCat.ofHom (algebraMap T O)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) =
        Spec.map (CommRingCat.ofHom (algebraMap S O)) := by
    rw [← Spec.map_comp]
    exact congrArg (fun f : S →+* O => Spec.map (CommRingCat.ofHom f))
      (IsScalarTower.algebraMap_eq S T O).symm
  have hst : (IsScalarTower.toAlgHom R S T : S →+* T) = algebraMap S T := rfl
  have hto : (IsScalarTower.toAlgHom R T O : T →+* O) = algebraMap T O := rfl
  have hso : (IsScalarTower.toAlgHom R S O : S →+* O) = algebraMap S O := rfl
  simpa only [hst, hto, hso, ← Category.assoc, hq, smoothHorizontalIntegralPoint] using h

end FLT.Mazur.WeierstrassIntegralChart
