/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneLaurentBoundary
public import FLT.Mazur.WeierstrassCoefficientShearRootLaurentOverlap
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
public import FLT.Mazur.WeierstrassCoefficientShearTerminalLaurent
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins
public import FLT.Mazur.WeierstrassCoefficientShearConicParameters
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalOverlap
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# The scale-one terminal boundary in the actual coefficient gluing

The complete Laurent chart attaches to the entire last retained conic
through the actual integral tensor transition at the original final stage.
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
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "conic" => coefficientShearRetainedScaleOneConic hπ data S r j hj 0 hj
  hs hp h3 h4 hr
local notation "N" => coefficientShearTerminalLaurent
  hπ data S r (j + 1) hj hsNext h3 h4 hc hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "ψ" => tensorShearScaleOneTerminalLaurentConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearScaleOneConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalLaurentEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr hc a ha

/-- The entire Laurent boundary and retained conic agree in the actual coefficient gluing. -/
@[reassoc] theorem coefficientShearScaleOneLaurentConic_boundary : b ≫ N = inc ≫ conic := by
  apply (cancel_mono (G).hom).mp
  simp only [Category.assoc]
  rw [coefficientShearRootTerminalLaurent_reconstruction (hp := hp)]
  erw [tensorShearScaleOneTerminalLaurentConicMap_boundary_assoc
    W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha]
  erw [globalTensor_depthOverlap hπ data S j hj]
  rw [← Category.assoc, tensorShearScaleOneConicBoundaryIso_inclusion]
  change _ = inc ≫ _ ≫
    coefficientShearRetainedTensorChart hπ data S r (j + 1) hj
      ⟨j, Nat.lt_succ_self j⟩ ≫ (G).hom
  rw [coefficientShearRootTerminalRetained_reconstruction, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
