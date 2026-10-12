/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootInitialOverlap
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
/-!
# Independent initial projective components over arbitrary splitting fields

Glue the actual entire conic parameters and retained lines only after proving
their signed reciprocal overlaps. Both original affine origins are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
variable (hs : algebraMap R S (π ^ start) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (g3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (g4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (g6 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "conic" => coefficientShearInitialConic hπ data S r (1 + m) hm hs g3 g4 hr
local notation "E" => conicZeroAffineIso c g6
local notation "F₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "F₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "line" => coefficientShearRetainedLine hπ data S r (1 + m) hm
  (Fin.mk 0 (by omega : 0 < 1 + m)) hs hp h3 h4 hr
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)
local notation "G" => coefficientShearGluedIso hπ data S r (1 + m) hm

/-- The complete first initial projective component for an arbitrary tangent root. -/
def coefficientShearRootInitialFirstComponent :
    ProjectiveLine.scheme S ⟶ coefficientShearGlued hπ data S r (1 + m) hm :=
  ProjectiveLine.scaledReciprocalDesc a⁻¹ F₁ L₁
    (coefficientShearRootInitialFirst_overlap hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha)

local notation "C₁" => coefficientShearRootInitialFirstComponent
  hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha

/-- The left chart retains the entire first initial conic parameter. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_left :
    ProjectiveLine.left S ≫ C₁ = F₁ := ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- The right chart retains the first line with its actual signed reciprocal scale. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_right :
    ProjectiveLine.right S ≫ C₁ = ProjectiveLine.chartScaling S a⁻¹ ≫ L₁ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The zero marking is the original full conic parameter origin. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_zero :
    ProjectiveLine.zero S ≫ C₁ = ProjectiveLine.chartZero S ≫ F₁ :=
  ProjectiveLine.scaledReciprocalDesc_zero _ _ _ _

/-- The infinity marking is the original retained line origin. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_infinity :
    ProjectiveLine.infinity S ≫ C₁ = ProjectiveLine.chartZero S ≫ L₁ :=
  ProjectiveLine.scaledReciprocalDesc_infinity _ _ _ _

/-- The complete second initial projective component for an arbitrary tangent root. -/
def coefficientShearRootInitialSecondComponent :
    ProjectiveLine.scheme S ⟶ coefficientShearGlued hπ data S r (1 + m) hm :=
  ProjectiveLine.scaledReciprocalDesc (-a)⁻¹ F₂ L₂
    (coefficientShearRootInitialSecond_overlap hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha)

local notation "C₂" => coefficientShearRootInitialSecondComponent
  hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha

/-- The left chart retains the entire second initial conic parameter. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_left :
    ProjectiveLine.left S ≫ C₂ = F₂ := ProjectiveLine.scaledReciprocalDesc_left _ _ _ _

/-- The right chart retains the second line with its actual signed reciprocal scale. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_right :
    ProjectiveLine.right S ≫ C₂ = ProjectiveLine.chartScaling S (-a)⁻¹ ≫ L₂ :=
  ProjectiveLine.scaledReciprocalDesc_right _ _ _ _

/-- The zero marking is the original full conic parameter origin. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_zero :
    ProjectiveLine.zero S ≫ C₂ = ProjectiveLine.chartZero S ≫ F₂ :=
  ProjectiveLine.scaledReciprocalDesc_zero _ _ _ _

/-- The infinity marking is the original retained line origin. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_infinity :
    ProjectiveLine.infinity S ≫ C₂ = ProjectiveLine.chartZero S ≫ L₂ :=
  ProjectiveLine.scaledReciprocalDesc_infinity _ _ _ _

local notation "g" => coefficientShearGluedStructure hπ data S r (1 + m) hm
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap S (ConicParameterOpen c)))

/-- The full first conic parameter retains the actual coefficient structure. -/
@[reassoc] theorem coefficientShearRootInitialFirstParameter_structure :
    coefficientConicFirstParameter (U).a₁ c hu conic ≫ g = b := by
  rw [coefficientConicFirstParameter, Category.assoc, Category.assoc,
    coefficientShearInitialConic_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom S (ConicCoordinate (U).a₁ c) (ConicFirstOpen (U).a₁ c))]
  exact terminalComponent_algebra_structure
    (conicFirstParameterEquiv (U).a₁ c hu).symm.toAlgHom

/-- Both charts of the first projective component are over the original coefficient field. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_structure :
    C₁ ≫ g = ProjectiveLine.toBase S := by
  apply pushout.hom_ext
  · change ProjectiveLine.left S ≫ C₁ ≫ g = ProjectiveLine.left S ≫ ProjectiveLine.toBase S
    rw [coefficientShearRootInitialFirstComponent_left_assoc,
      coefficientShearRootInitialFirstParameter_structure (a := a) (ha := ha),
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right S ≫ C₁ ≫ g = ProjectiveLine.right S ≫ ProjectiveLine.toBase S
    rw [coefficientShearRootInitialFirstComponent_right_assoc,
      coefficientShearRetainedLine_structure, ProjectiveLine.right_toBase]
    exact ProjectiveLine.chartScaling_toBase S a⁻¹

/-- The full second conic parameter retains the actual coefficient structure. -/
@[reassoc] theorem coefficientShearRootInitialSecondParameter_structure :
    coefficientConicSecondParameter (U).a₁ c hu conic ≫ g = b := by
  rw [coefficientConicSecondParameter, Category.assoc, Category.assoc,
    coefficientShearInitialConic_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom S (ConicCoordinate (U).a₁ c) (ConicSecondOpen (U).a₁ c))]
  exact terminalComponent_algebra_structure
    (conicSecondParameterEquiv (U).a₁ c hu).symm.toAlgHom

/-- Both charts of the second projective component are over the original coefficient field. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_structure :
    C₂ ≫ g = ProjectiveLine.toBase S := by
  apply pushout.hom_ext
  · change ProjectiveLine.left S ≫ C₂ ≫ g = ProjectiveLine.left S ≫ ProjectiveLine.toBase S
    rw [coefficientShearRootInitialSecondComponent_left_assoc,
      coefficientShearRootInitialSecondParameter_structure (a := a) (ha := ha),
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right S ≫ C₂ ≫ g = ProjectiveLine.right S ≫ ProjectiveLine.toBase S
    rw [coefficientShearRootInitialSecondComponent_right_assoc,
      coefficientShearRetainedLine_structure, ProjectiveLine.right_toBase]
    exact ProjectiveLine.chartScaling_toBase S (-a)⁻¹

end FLT.Mazur.WeierstrassDividedDepth
