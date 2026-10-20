/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalInfinityCoverage

/-!
# Opposite divided branches are covered at their unramified points

Equal-abscissa opposite inputs with unit vertical derivative have unit
ordinate difference. They therefore lie in the actual resolved reciprocal
domain, whose output contracts to the original infinity section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "H" => WeierstrassDilatation.Coordinate W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "V" => finiteResolvedReciprocalOutputOpen hπ data j hj

/-- Opposite inputs with unit vertical derivative lie in the actual resolved addition domain. -/
theorem finiteResolvedReciprocalOpposite_coverage (a c : H →ₐ[R] S)
    (hy : c (y W s (d).b3 (d).b4 (d).b6) =
      -a (y W s (d).b3 (d).b4 (d).b6) - algebraMap R S W.a₁ *
        a (x W s (d).b3 (d).b4 (d).b6) - algebraMap R S (d).b3)
    (hd : IsUnit (2 * a (y W s (d).b3 (d).b4 (d).b6) + algebraMap R S W.a₁ *
      a (x W s (d).b3 (d).b4 (d).b6) + algebraMap R S (d).b3))
    (hx : a (x W s (d).b3 (d).b4 (d).b6) = c (x W s (d).b3 (d).b4 (d).b6))
    (p : Spec (.of S) ⟶ finiteResolvedProduct hπ data j hj)
    (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ finiteSecantDividedChart hπ data j hj =
      p ≫ pullback.fst t t ≫ (U).ι)
    (hc : Spec.map (CommRingCat.ofHom c.toRingHom) ≫ finiteSecantDividedChart hπ data j hj =
      p ≫ pullback.snd t t ≫ (U).ι) :
    ∃ k : Spec (.of S) ⟶ (V).toScheme,
      k ≫ finiteResolvedReciprocalDomainMap hπ data j hj = p ∧
      k ≫ finiteResolvedReciprocalAddition hπ data j hj ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
        Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W := by
  have hu : IsUnit (a (y W s (d).b3 (d).b4 (d).b6) - c (y W s (d).b3 (d).b4 (d).b6)) := by
    convert hd using 1
    rw [hy]
    ring
  exact finiteResolvedReciprocalInfinity_coverage hπ data j hj a c hu hx p ha hc

end FLT.Mazur.WeierstrassDividedDepth
