/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeOrigin
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeMaps

/-!
# The ordered positive-depth incidence points

The origins of the full middle nodes give tensor-algebra points with exact
coordinates (0,0,0) and (0,-a₁,0). Their ordering survives every nonzero extension.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "c" => residue R b6
/-- The first tensor incidence point is the first full node's origin. -/
def residueFirstIncidencePoint : T →ₐ[K] K :=
  (middleNodeOrigin c).comp (residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4)

/-- The second tensor incidence point is the opposite full node's origin. -/
def residueSecondIncidencePoint : T →ₐ[K] K :=
  (middleNodeOrigin c).comp (residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4)

local notation "first" => residueFirstIncidencePoint D k hk0 hk b3 b4 b6 h3 h4
local notation "second" => residueSecondIncidencePoint D k hk0 hk b3 b4 b6 h3 h4

/-- The first point retains the ordered zero slope and both branch equations. -/
theorem residueFirstIncidencePoint_coord (i : Fin 3) :
    first (tensorCoord W (π ^ k) π b3 b4 b6 K i) = 0 := by
  change middleNodeOrigin c (residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 _) = 0
  rw [residueFirstNodeMap_coord]
  fin_cases i
  · exact middleNodeOrigin_t c _
  · exact middleNodeOrigin_v c _
  · exact middleNodeOrigin_u c

/-- The second point retains precisely the opposite original tangent slope. -/
theorem residueSecondIncidencePoint_coord (i : Fin 3) :
    second (tensorCoord W (π ^ k) π b3 b4 b6 K i) = ![0, -residue R W.a₁, 0] i := by
  change middleNodeOrigin c (residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 _) = _
  rw [residueSecondNodeMap_coord]
  fin_cases i
  · exact middleNodeOrigin_t c _
  · change middleNodeOrigin c
      (-middleNodeV (residue R W.a₁) c - algebraMap K _ (residue R W.a₁)) = -residue R W.a₁
    rw [map_sub, map_neg, middleNodeOrigin_v, AlgHom.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, neg_zero, zero_sub]
  · exact middleNodeOrigin_u c

/-- The actual first node chart sends its origin to this tensor point. -/
@[reassoc] theorem residueMiddleFirstNodeChart_origin :
    Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) ≫
      residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
        Spec.map (CommRingCat.ofHom (AlgHom.toRingHom first)) := by
  rw [residueMiddleFirstNodeChart_eq_spec, ← Spec.map_comp]
  rfl

/-- The actual opposite node chart sends its origin to the opposite tensor point. -/
@[reassoc] theorem residueMiddleSecondNodeChart_origin :
    Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) ≫
      residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
        Spec.map (CommRingCat.ofHom (AlgHom.toRingHom second)) := by
  rw [residueMiddleSecondNodeChart_eq_spec, ← Spec.map_comp]
  rfl

/-- Nonzero coefficient extensions preserve both original tangent markings. -/
theorem residueIncidencePoints_extension_ne (S : Type u) [CommRing S] [Nontrivial S]
    [Algebra K S] :
    Spec.map (CommRingCat.ofHom (algebraMap K S)) ≫
        Spec.map (CommRingCat.ofHom (AlgHom.toRingHom first)) ≠
      Spec.map (CommRingCat.ofHom (algebraMap K S)) ≫
        Spec.map (CommRingCat.ofHom (AlgHom.toRingHom second)) := by
  intro h
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have hv := congrArg (fun f => f.hom (tensorCoord W (π ^ k) π b3 b4 b6 K 1))
    (Spec.map_injective h)
  change algebraMap K S (first _) = algebraMap K S (second _) at hv
  rw [residueFirstIncidencePoint_coord, residueSecondIncidencePoint_coord,
    Matrix.cons_val_one, Matrix.cons_val_zero, map_zero, map_neg] at hv
  exact ((D.a₁_unit.map (residue R)).map (algebraMap K S)).ne_zero
    (neg_eq_zero.mp hv.symm)

end FLT.Mazur.WeierstrassSuccessiveX
