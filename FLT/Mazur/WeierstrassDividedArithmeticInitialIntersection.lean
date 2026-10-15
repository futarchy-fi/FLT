/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryCharts

/-!
# Exact initial chart intersections in arithmetic stages

At every quotient order and retention depth, the original initial and first
successive charts meet in exactly their full common principal tensor boundary.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonArithmeticStages
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m : ℕ)
  (h1 : 1 ≤ n) (r : ℕ) (hr : 1 + r ≤ n)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t a
local notation "B" => PrincipalOpenTensor.transitionIso Q x u b

/-- The full initial boundary is the exact intersection in the actual arithmetic stage. -/
theorem initialArithmeticTensor_isPullback :
    IsPullback ((A).inv ≫ PrincipalOpenTensor.inclusion Q t)
      ((B).inv ≫ PrincipalOpenTensor.inclusion Q u)
      (finiteArithmeticInitialTensorChart hπ data m (1 + r) hr)
      (finiteArithmeticOlderTensorChart hπ data m 0 h1 r hr) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (pullbackSymmetry q (finiteGlobalStructure hπ data (1 + r) hr)).hom
    (initialRetainedGlobalTensor_isPullback hπ data Q h1 r hr).cone
    (initialRetainedGlobalTensor_isPullback hπ data Q h1 r hr).isLimit)

/-- The original whole tensor boundary is isomorphic to the arithmetic fiber product. -/
def initialArithmeticTensorPullbackIso :=
  (initialArithmeticTensor_isPullback hπ data m h1 r hr).isoPullback

/-- The intersection isomorphism retains the original initial boundary projection. -/
@[reassoc] theorem initialArithmeticTensorPullbackIso_initial :
    (initialArithmeticTensorPullbackIso hπ data m h1 r hr).hom ≫
      pullback.fst _ _ = (A).inv ≫ PrincipalOpenTensor.inclusion Q t :=
  (initialArithmeticTensor_isPullback hπ data m h1 r hr).isoPullback_hom_fst

/-- The intersection isomorphism retains the original first successive projection. -/
@[reassoc] theorem initialArithmeticTensorPullbackIso_successive :
    (initialArithmeticTensorPullbackIso hπ data m h1 r hr).hom ≫
      pullback.snd _ _ = (B).inv ≫ PrincipalOpenTensor.inclusion Q u :=
  (initialArithmeticTensor_isPullback hπ data m h1 r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
