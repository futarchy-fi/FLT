/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalConicIntersection
public import FLT.Mazur.WeierstrassSuccessiveXResidueConicBoundaryCoordinates

/-!
# Original divided functions on the full global conic intersection

Identify the actual fiber-product projection with the algebra map carrying
x to reciprocal incidence and y to the oriented slope ratio. This retains
every original function, including the map used by both terminal transitions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
section Local
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
open WeierstrassSuccessiveX

/-- The local spectrum transition is the restriction of every original divided function. -/
theorem conicCoordinateProjection_spec :
    (residueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      Spec.map (CommRingCat.ofHom
        (residueMiddleTransition D k hk0 hk b3 b4 b6 h3 h4).toRingHom) ≫
      PrincipalOpenTensor.inclusion (ResidueField R)
        (WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6) =
      Spec.map (CommRingCat.ofHom
        (residueDividedConicMap D k hk b3 b4 b6 h3 h4).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.op_hom,
    Quiver.Hom.unop_op, RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom,
    RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgHom.coe_toRingHom]
  simp only [residueDividedConicMap, residueMiddleConicOpenEquiv,
    residueMiddleTransition, residueDividedConicOpenEquiv, middleDividedConicOverlap,
    AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom]
  congr 3

end Local

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "m" => WeierstrassSuccessiveX.residueMiddleTransition D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "hk'" => Nat.zero_lt_succ (start + j)

open WeierstrassSuccessiveX WeierstrassModificationX
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 d)
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)

local notation "f" => globalDividedTensorChart hπ data K (j + 1) hj

local notation "A₀" => WeierstrassDilatation.ScalarExtension W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "φ" => residueDividedConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)

omit [IsBezout R] in
/-- The actual intersection projection is exactly the map with the proved original coordinates. -/
theorem conicToDivided_eq_spec : conicToDivided data D j hj hk0 hk =
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom φ)) := by
  exact conicCoordinateProjection_spec D (start + j) hk0 hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)

/-- The explicit original-coordinate map presents the entire global divided-conic intersection. -/
theorem globalDividedConicCoordinates_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom φ))) i f (C ≫ g) := by
  rw [← conicToDivided_eq_spec data D j hj hk0 hk]
  exact globalDividedConic_isPullback hπ data D j hj hk0 hk

/-- The original-coordinate map retains the actual global conic inclusion on the full boundary. -/
theorem globalDividedConicCoordinates_chart :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom φ)) ≫ f = i ≫ C ≫ g := by
  exact (globalDividedConicCoordinates_isPullback hπ data D j hj hk0 hk).w

end FLT.Mazur.WeierstrassDividedDepth
