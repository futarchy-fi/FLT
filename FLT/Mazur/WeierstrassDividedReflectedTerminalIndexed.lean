/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedIndexed
public import FLT.Mazur.WeierstrassDividedReflectedTerminalOutput

/-!
# Reindex the actual even-terminal reflected residue criterion

Transport the actual-map derivative calculation to the finite family's
numerically equal index without unfolding its localization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (d : Data W π k) (e : Data W π l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
  [IsDomain R] [IsLocalRing R] [Module.Flat R S] (D : SplitNodeDepth W π m)
  (hkl : k ≤ l) (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  {r : ℕ} (z : Data W π r) (hr : r = m - k - l) (h2 : W.a₂ = 0)
local notation "B" => SumDepthSourceRing d e a c
local notation "j" => IsScalarTower.toAlgHom R S B

/-- The actual reindexed output retains the same explicit residue smoothness criterion. -/
theorem reflectedSourceOutputAt_terminal_vertical {K : Type u} [Field K] [Algebra R K]
    (ρ : B →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
    (ht : algebraMap R K (π ^ (l - k)) = 0)
    (hm0 : m = 2 * l) (hl0 : algebraMap R K (π ^ l) = 0)
    (he3 : algebraMap R K e.b3 = 0) (he4 : algebraMap R K e.b4 = 0)
    (hz3 : algebraMap R K z.b3 = 0)
    (hy : ρ (((j).comp a) (y W (π ^ k) d.b3 d.b4 d.b6)) = 0)
    (ha : algebraMap R K W.a₁ ≠ 0) :
    ρ (reflectedSourceOutputAt d e a c D hkl hl hm z hr h2
      (verticalDerivative W (π ^ r) z.b3 z.b4 z.b6)) ≠ 0 := by
  subst r
  exact nodeReflectedOutput_terminal_vertical D d e hkl hl hm z h2
    ((j).comp a) ((j).comp c) (sumDepthSource_leftUnit d e a c)
    (sumDepthSource_rightUnit d e a c) (sumDepthSource_abscissaUnit d e a c)
    (sumDepthSourceInverse d e a c D.uniformizer_ne_zero hkl)
    (sumDepthSourceSlope d e a c D.uniformizer_ne_zero hkl)
    (sumDepthSourceInverse_relation d e a c D.uniformizer_ne_zero hkl)
    (sumDepthSourceSlope_relation d e a c D.uniformizer_ne_zero hkl)
    ρ hm0 hs ht hl0 he3 he4 hz3 hy ha

end FLT.Mazur.WeierstrassDividedDepth
