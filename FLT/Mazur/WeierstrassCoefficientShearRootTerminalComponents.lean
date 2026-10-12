/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalOverlap
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Independent arbitrary-root terminal projective components

Glue each complete conic parameter to the opposite full terminal branch
using the proved reciprocal overlap, retaining both origins and structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j)) hs hp h3 h4 hr
local notation "E" => conicZeroAffineIso c h6
local notation "P₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "P₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "N" => coefficientShearTerminalNode
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "B₁" => coefficientShearTerminalFirstBranch
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "B₂" => coefficientShearTerminalSecondBranch
  hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "ψ" => tensorShearTerminalNodeConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr h6 a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalNodeEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha

/-- The first full terminal component, constructed from its actual entire affine charts. -/
def coefficientShearRootTerminalFirstComponent :
    ProjectiveLine.scheme S ⟶ coefficientShearGlued hπ data S r (j + 1) hj :=
  pushout.desc P₁ B₂
    (coefficientShearRootTerminalFirst_overlap hπ data S r j hj hs hp h3 h4 h6 hr a ha)

local notation "C₁" => coefficientShearRootTerminalFirstComponent
  hπ data S r j hj hs hp h3 h4 h6 hr a ha

/-- The full first conic parameter survives on the left chart. -/
@[reassoc] theorem coefficientShearRootTerminalFirstComponent_left :
    ProjectiveLine.left S ≫ C₁ = P₁ := pushout.inl_desc _ _ _

/-- The complete opposite node branch survives on the right chart. -/
@[reassoc] theorem coefficientShearRootTerminalFirstComponent_right :
    ProjectiveLine.right S ≫ C₁ = B₂ := pushout.inr_desc _ _ _

/-- The second full terminal component retains the opposite order of its affine charts. -/
def coefficientShearRootTerminalSecondComponent :
    ProjectiveLine.scheme S ⟶ coefficientShearGlued hπ data S r (j + 1) hj :=
  pushout.desc P₂ B₁
    (coefficientShearRootTerminalSecond_overlap hπ data S r j hj hs hp h3 h4 h6 hr a ha)

local notation "C₂" => coefficientShearRootTerminalSecondComponent
  hπ data S r j hj hs hp h3 h4 h6 hr a ha

/-- The full second conic parameter survives on the left chart. -/
@[reassoc] theorem coefficientShearRootTerminalSecondComponent_left :
    ProjectiveLine.left S ≫ C₂ = P₂ := pushout.inl_desc _ _ _

/-- The complete first node branch survives on the right chart. -/
@[reassoc] theorem coefficientShearRootTerminalSecondComponent_right :
    ProjectiveLine.right S ≫ C₂ = B₁ := pushout.inr_desc _ _ _

/-- The first zero marking is the original full conic parameter origin. -/
@[reassoc] theorem coefficientShearRootTerminalFirstComponent_zero :
    ProjectiveLine.zero S ≫ C₁ = ProjectiveLine.chartZero S ≫ P₁ := by
  rw [ProjectiveLine.zero, Category.assoc, coefficientShearRootTerminalFirstComponent_left]

/-- The second zero marking is the opposite original full conic parameter origin. -/
@[reassoc] theorem coefficientShearRootTerminalSecondComponent_zero :
    ProjectiveLine.zero S ≫ C₂ = ProjectiveLine.chartZero S ≫ P₂ := by
  rw [ProjectiveLine.zero, Category.assoc, coefficientShearRootTerminalSecondComponent_left]

/-- The first infinity marking is the actual common terminal node. -/
@[reassoc] theorem coefficientShearRootTerminalFirstComponent_infinity :
    ProjectiveLine.infinity S ≫ C₁ =
      coefficientShearTerminalOrigin hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha := by
  rw [ProjectiveLine.infinity, Category.assoc, coefficientShearRootTerminalFirstComponent_right,
    coefficientShearTerminalSecondBranch_origin]

/-- The second infinity marking is the same actual terminal node. -/
@[reassoc] theorem coefficientShearRootTerminalSecondComponent_infinity :
    ProjectiveLine.infinity S ≫ C₂ =
      coefficientShearTerminalOrigin hπ data S r (j + 1) hj hsNext h3 h4 h6 hr a ha := by
  rw [ProjectiveLine.infinity, Category.assoc, coefficientShearRootTerminalSecondComponent_right,
    coefficientShearTerminalFirstBranch_origin]

local notation "g" => coefficientShearGluedStructure hπ data S r (j + 1) hj
local notation "base" => Spec.map (CommRingCat.ofHom (algebraMap S (ConicParameterOpen c)))

/-- The whole first terminal parameter preserves the coefficient structure. -/
@[reassoc] theorem coefficientShearRootTerminalFirstParameter_structure :
    coefficientConicFirstParameter (U).a₁ c hu conic ≫ g = base := by
  rw [coefficientConicFirstParameter, Category.assoc, Category.assoc,
    coefficientShearRetainedConic_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom S (ConicCoordinate (U).a₁ c) (ConicFirstOpen (U).a₁ c))]
  exact terminalComponent_algebra_structure
    (conicFirstParameterEquiv (U).a₁ c hu).symm.toAlgHom

/-- The whole second terminal parameter preserves the coefficient structure. -/
@[reassoc] theorem coefficientShearRootTerminalSecondParameter_structure :
    coefficientConicSecondParameter (U).a₁ c hu conic ≫ g = base := by
  rw [coefficientConicSecondParameter, Category.assoc, Category.assoc,
    coefficientShearRetainedConic_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom S (ConicCoordinate (U).a₁ c) (ConicSecondOpen (U).a₁ c))]
  exact terminalComponent_algebra_structure
    (conicSecondParameterEquiv (U).a₁ c hu).symm.toAlgHom

/-- Both charts of the complete first terminal component are over the coefficient field. -/
@[reassoc] theorem coefficientShearRootTerminalFirstComponent_structure :
    C₁ ≫ g = ProjectiveLine.toBase S := by
  apply pushout.hom_ext
  · change ProjectiveLine.left S ≫ C₁ ≫ g = ProjectiveLine.left S ≫ ProjectiveLine.toBase S
    rw [coefficientShearRootTerminalFirstComponent_left_assoc,
      coefficientShearRootTerminalFirstParameter_structure (a := a) (ha := ha),
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right S ≫ C₁ ≫ g = ProjectiveLine.right S ≫ ProjectiveLine.toBase S
    rw [coefficientShearRootTerminalFirstComponent_right_assoc,
      coefficientShearTerminalSecondBranch_structure, ProjectiveLine.right_toBase]

/-- Both charts of the complete second terminal component are over the coefficient field. -/
@[reassoc] theorem coefficientShearRootTerminalSecondComponent_structure :
    C₂ ≫ g = ProjectiveLine.toBase S := by
  apply pushout.hom_ext
  · change ProjectiveLine.left S ≫ C₂ ≫ g = ProjectiveLine.left S ≫ ProjectiveLine.toBase S
    rw [coefficientShearRootTerminalSecondComponent_left_assoc,
      coefficientShearRootTerminalSecondParameter_structure (a := a) (ha := ha),
      conicZeroAffineIso_structure, ProjectiveLine.left_toBase]
  · change ProjectiveLine.right S ≫ C₂ ≫ g = ProjectiveLine.right S ≫ ProjectiveLine.toBase S
    rw [coefficientShearRootTerminalSecondComponent_right_assoc,
      coefficientShearTerminalFirstBranch_structure, ProjectiveLine.right_toBase]

end FLT.Mazur.WeierstrassDividedDepth
