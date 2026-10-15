/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalNodeBoundary
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalCoverage

/-!
# The normalized terminal node in the original global arithmetic atlas

Both normalized Laurent maps are the exact global branch intersections.
Their union is the inverse image of the original divided horizontal open.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q

variable (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d)

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6) (opposite : Bool)
local notation "s" => π ^ (start + j + 1)
local notation "U" => W.map q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "r" => WeierstrassDilatation.terminalTangentRoot U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "hrI" => WeierstrassDilatation.terminalTangentRoot_mem U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "hr" => WeierstrassDilatation.terminalTangentRoot_equation U (q s) J hJ (ha.map q)
  (arithmeticCoefficient_mem π m hs₂) (arithmeticCoefficient_mem π m h2)
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "v" => arithmeticBranchSlope π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "hv" => arithmeticBranchSlope_equation π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "G" => tensorTerminalLaurent W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q v hv
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6

local notation "E" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6 opposite)))
local notation "B" => terminalArithmeticBranchBoundary data m j hj ha hs h2 h3 h4 h6 opposite

/-- The normalized restriction retains the entire original horizontal-open image. -/
theorem terminalArithmeticNodeEvaluation_image (p : Spec (.of (NodalFiber.Coordinate c))) :
    (∃ (label : Bool), ∃ z, Spec.map (CommRingCat.ofHom
      (terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6 label).toRingHom) z = p) ↔
        ∃ y, PrincipalOpenTensor.inclusion Q x y = (e).hom p := by
  rw [← terminalArithmeticBoundaries_image data m j hj ha hs h2 h3 h4 h6]
  constructor
  · rintro ⟨label, z, rfl⟩
    refine ⟨label, z, ?_⟩
    exact (congrArg (fun f ↦ f z)
      (terminalArithmeticNodeEvaluation_boundary data m j hj ha hs h2 h3 h4 h6 label)).symm
  · rintro ⟨label, z, hz⟩
    refine ⟨label, z, ?_⟩
    have h := congrArg (fun f ↦ f z)
      (terminalArithmeticNodeEvaluation_boundary data m j hj ha hs h2 h3 h4 h6 label)
    have he := congrArg (fun z ↦ (e).inv z) (h.trans hz)
    have hi (z : Spec (.of (NodalFiber.Coordinate c))) : (e).inv ((e).hom z) = z :=
      congrArg (fun f ↦ f z) (e).hom_inv_id
    exact (hi _).symm.trans (he.trans (hi p))

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)
local notation "C₀" => arithmeticTensorBranchChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite

/-- Both normalized boundaries are the exact branch intersections in the original global model. -/
theorem terminalArithmeticNodeEvaluation_isPullback :
    IsPullback E (PolygonSmoothing.leftBranchOpen Q (parameter R π m))
      ((e).hom ≫ finiteArithmeticDividedTensorChart hπ data m (j + 1) hj)
      (C₀ ≫ finiteArithmeticNewestTensorChart hπ data m j hj) := by
  have H := terminalArithmeticBranch_isPullback hπ data m j hj ha hs h2 h3 h4 h6 opposite
  apply H.of_iso (Iso.refl _) (e).symm (Iso.refl _) (Iso.refl _)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rw [← terminalArithmeticNodeEvaluation_boundary data m j hj ha hs h2 h3 h4 h6 opposite]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · simp
  · simp
  · simp

/-- The normalized full boundary commutes with the actual global chart maps for either label. -/
@[reassoc] theorem terminalArithmeticNodeEvaluation_chart :
    E ≫ (e).hom ≫ finiteArithmeticDividedTensorChart hπ data m (j + 1) hj =
      PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫ C₀ ≫
        finiteArithmeticNewestTensorChart hπ data m j hj :=
  (terminalArithmeticNodeEvaluation_isPullback data m j hj ha hs h2 h3 h4 h6 opposite hπ).w

end FLT.Mazur.WeierstrassDividedDepth
