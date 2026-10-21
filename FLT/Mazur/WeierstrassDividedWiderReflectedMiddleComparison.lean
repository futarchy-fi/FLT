/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedWiderReflectedIndexed
public import FLT.Mazur.WeierstrassDividedWiderReflectedContraction
public import FLT.Mazur.WeierstrassDividedCommonSumContraction
public import FLT.Mazur.WeierstrassDilatationLifting

/-!
# Agreement with the common sum output at the middle boundary

At m=2*(k+l), reflected depth equals sum depth. Both actual source outputs
contract to the same original secant. Regularity identifies their complete
coordinate maps; the existing common-sum middle coverage remains reusable.
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
  [IsDomain R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (hm : k + 2 * l ≤ m) (htop : m ≤ 2 * (k + l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "B" => SumDepthSourceRing d e a c
local notation "res" => sumDepthSourceRestriction d e a c D.uniformizer_ne_zero hkl
local notation "old" => dividedSecantOutput W (π ^ k) d.b3 d.b4 d.b6 a
  (unequalDepthRight D.uniformizer_ne_zero d e hkl c) d.factor3 d.factor4 d.factor6

/-- The complete indexed algebra output has the same original-coordinate contraction. -/
theorem widerReflectedSourceOutputAt_original {r : ℕ} (z : Data W π r)
    (hr : r = m - k - l) :
    (widerReflectedSourceOutputAt d e a c D hkl hm htop z hr h2).comp
      (fromOriginal W (π ^ r) z.b3 z.b4 z.b6 z.factor3 z.factor4 z.factor6) =
        (res).comp old := by
  subst r
  exact widerReflectedSourceOutput_original d e a c D hkl hm htop z h2

variable (z : Data W π (k + l)) (hmid : m = 2 * (k + l))
  (dd : BranchQuotientData d) (ee : CommonBranchData e k)

/-- At the middle boundary the wider reflected output is the existing common sum output. -/
theorem widerReflectedSourceOutputAt_eq_common :
    widerReflectedSourceOutputAt d e a c D hkl hm htop z (by omega) h2 =
      commonSumDepthSourceOutput d e a c D.uniformizer_ne_zero hkl dd ee z h2 := by
  have hreg : IsRegular (algebraMap R B (π ^ (k + l))) :=
    WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (isRegular_iff_ne_zero.mpr (pow_ne_zero _ D.uniformizer_ne_zero))
  apply lift_unique W (π ^ (k + l)) z.b3 z.b4 z.b6
    z.factor3 z.factor4 z.factor6 hreg
  rw [widerReflectedSourceOutputAt_original, commonSumDepthSourceOutput_original]

/-- The two boundary outputs agree as scheme morphisms on the whole principal open. -/
theorem widerReflectedSourceLiftAt_eq_common :
    widerReflectedSourceLiftAt d e a c D hkl hm htop z (by omega) h2 =
      commonSumDepthSourceLift d e a c D.uniformizer_ne_zero hkl dd ee z h2 := by
  unfold widerReflectedSourceLiftAt commonSumDepthSourceLift
  rw [widerReflectedSourceOutputAt_eq_common D d e hkl hm htop h2 a c z hmid dd ee]

end FLT.Mazur.WeierstrassDividedDepth
