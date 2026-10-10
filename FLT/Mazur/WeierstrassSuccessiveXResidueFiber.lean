/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChangeCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXParameterEquiv
public import FLT.Mazur.WeierstrassSuccessiveXSplitFiber
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# Actual successive tensor residue fibers before the middle depth

At positive preceding depth the scale and parameter vanish. Before the
middle depth the three divided coefficients vanish too. The actual tensor
fiber is therefore an ordered pair of full incidence nodes, retaining t and u.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) < n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "B" => SuccessiveIncidence.Coordinate (0 : K)

/-- The actual extended residue equation has all five modification parameters zero. -/
def residueZeroEquiv : ExtendedCoordinate W (π ^ k) π b3 b4 b6 K ≃ₐ[K]
    Coordinate (W.map (residue R)) 0 0 0 0 0 := by
  obtain ⟨hb3, hb4⟩ := WeierstrassDilatation.divided_linear_mem D (k + 1)
    (Nat.le_of_lt hk) b3 b4 h3 h4
  apply parameterEquiv _ _ _ _ _ _ _ _ _ _ _
  · exact WeierstrassDilatation.residue_scale_eq_zero D k hk0
  · exact (residue_eq_zero_iff _).mpr
      (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  · exact (residue_eq_zero_iff _).mpr hb3
  · exact (residue_eq_zero_iff _).mpr hb4
  · exact (residue_eq_zero_iff _).mpr
      (WeierstrassDilatation.divided_constant_mem D (k + 1) hk b6 h6)

/-- All actual extended residue coordinates are retained by the zero-parameter comparison. -/
@[simp] theorem residueZeroEquiv_coord (i : Fin 3) :
    residueZeroEquiv D k hk0 hk b3 b4 b6 h3 h4 h6
      (extendedCoord W (π ^ k) π b3 b4 b6 K i) =
        coord (W.map (residue R)) 0 0 0 0 0 i :=
  parameterEquiv_coord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i

/-- The actual tensor residue fiber is the ordered disjoint pair of incidence nodes. -/
def residueNodesEquiv : ScalarExtension W (π ^ k) π b3 b4 b6 K ≃ₐ[K] B × B :=
  (baseChangeEquiv W (π ^ k) π b3 b4 b6 K).trans
    ((residueZeroEquiv D k hk0 hk b3 b4 b6 h3 h4 h6).trans
      (splitFiberEquiv (W.map (residue R))
        ((residue_eq_zero_iff _).mpr D.a₂_mem) (D.a₁_unit.map (residue R))))

/-- The original incidence ratio is retained on both actual tensor-fiber components. -/
@[simp] theorem residueNodesEquiv_t :
    residueNodesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6
      (tensorCoord W (π ^ k) π b3 b4 b6 K 0) =
        (SuccessiveIncidence.t (0 : K), SuccessiveIncidence.t (0 : K)) := by
  simp only [residueNodesEquiv, AlgEquiv.trans_apply, baseChangeEquiv_coord,
    residueZeroEquiv_coord, splitFiberEquiv_t]

/-- The ordered slope values in the actual tensor fiber are zero and minus the tangent unit. -/
@[simp] theorem residueNodesEquiv_v :
    residueNodesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6
      (tensorCoord W (π ^ k) π b3 b4 b6 K 1) =
        (0, -algebraMap K B (residue R W.a₁)) := by
  simp only [residueNodesEquiv, AlgEquiv.trans_apply, baseChangeEquiv_coord,
    residueZeroEquiv_coord, splitFiberEquiv_v]
  rfl

/-- The original horizontal coordinate survives on both components, including their nodes. -/
@[simp] theorem residueNodesEquiv_u :
    residueNodesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6
      (tensorCoord W (π ^ k) π b3 b4 b6 K 2) =
        (SuccessiveIncidence.u (0 : K), SuccessiveIncidence.u (0 : K)) := by
  simp only [residueNodesEquiv, AlgEquiv.trans_apply, baseChangeEquiv_coord,
    residueZeroEquiv_coord, splitFiberEquiv_u]

end FLT.Mazur.WeierstrassSuccessiveX
