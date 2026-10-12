/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalZeroBoundaryGeometry
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalOverlap
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
public import FLT.Mazur.WeierstrassCoefficientShearTerminalNode
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins
public import FLT.Mazur.WeierstrassCoefficientShearConicParameters
public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Arbitrary-root scale-one terminal conic overlaps in the complete coefficient model

The actual integral depth boundary attaches both full conic parameters to
opposite terminal branches, preserving their reciprocal coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
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
local notation "conic" => coefficientShearRetainedScaleOneConic hπ data S r j hj 0 hj hs hp h3 h4 hr
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
local notation "ψ" => tensorShearScaleOneTerminalNodeConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr h6 a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearScaleOneConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalNodeEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr h6 a ha

/-- The full normalized node boundary and retained conic agree in the actual coefficient gluing. -/
@[reassoc] theorem coefficientShearRootTerminalZeroConic_boundary : b ≫ N = inc ≫ conic := by
  apply (cancel_mono (G).hom).mp
  simp only [Category.assoc]
  rw [coefficientShearRootTerminalNode_reconstruction (hp := hp)]
  erw [tensorShearScaleOneTerminalNodeConicMap_boundary_assoc
    W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr h6 a ha]
  erw [globalTensor_depthOverlap hπ data S j hj]
  rw [← Category.assoc, tensorShearScaleOneConicBoundaryIso_inclusion]
  rw [coefficientShearRetainedScaleOneConic]
  simp only [Category.assoc]
  rw [coefficientShearRootTerminalRetained_reconstruction]

/-- The entire first terminal parameter meets the opposite branch by reciprocal gluing. -/
theorem coefficientShearRootTerminalZeroFirst_overlap :
    ProjectiveLine.overlapLeft S ≫ P₁ = ProjectiveLine.overlapRight S ≫ B₂ := by
  rw [coefficientConicFirstParameter, ← Category.assoc, conicZeroAffineIso_puncture]
  have H := conicBoundaryFirst_inclusion U c hu h6
  rw [← Category.assoc] at H
  rw [← Category.assoc, ← Category.assoc, ← H, Category.assoc]
  erw [← coefficientShearRootTerminalZeroConic_boundary
    hπ data S r j hj hs hp h3 h4 h6 hr a ha]
  rw [← Category.assoc, tensorShearScaleOneTerminalConicFirst_spec]
  rfl

/-- The entire second terminal parameter retains the opposite reciprocal branch. -/
theorem coefficientShearRootTerminalZeroSecond_overlap :
    ProjectiveLine.overlapLeft S ≫ P₂ = ProjectiveLine.overlapRight S ≫ B₁ := by
  rw [coefficientConicSecondParameter, ← Category.assoc, conicZeroAffineIso_puncture]
  have H := conicBoundarySecond_inclusion U c hu h6
  rw [← Category.assoc] at H
  rw [← Category.assoc, ← Category.assoc, ← H, Category.assoc]
  erw [← coefficientShearRootTerminalZeroConic_boundary
    hπ data S r j hj hs hp h3 h4 h6 hr a ha]
  rw [← Category.assoc, tensorShearScaleOneTerminalConicSecond_spec]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
