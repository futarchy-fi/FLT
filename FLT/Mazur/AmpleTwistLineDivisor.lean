/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveAmpleDegree
public import FLT.Mazur.AmpleCoherentVanishing
public import FLT.Mazur.LineSectionZeroDivisor
public import FLT.Mazur.IntegralCurveCartierFinite

/-!
# Full effective divisors representing arbitrary ample-twisted curve lines

Every line on a proper integral curve acquires a nonzero section after a
positive ample twist, in a degree where its first cohomology vanishes. Its
full zero ideal is Cartier, and untwisting its divisor line recovers the
original line by an actual isomorphism. No divisor-support replacement occurs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleSheafTensorAssociator ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor
variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f] (hd : topologicalKrullDim X = 1)
  {B L : X.Modules} (hB : AmpleLineBundle B) (hL : LocallyFreeRankOne L)

include hd hB hL in
/-- Every original line has an acyclic positive ample twist with a nonzero section. -/
theorem exists_acyclic_line_twist_nonzero_section :
    ∃ n : ℕ, 0 < n ∧ Subsingleton (ModuleScalarH f (tensor L (tensorPower B n)) 1) ∧
      ∃ s : Γ(tensor L (tensorPower B n), ⊤), s ≠ 0 := by
  let _ := hL.isFinitePresentation
  obtain ⟨N, hN⟩ := hB.coherent_vanishing f L
  obtain ⟨m, hm⟩ := exists_nat_gt (-curveEulerCharacteristic f L)
  let n := max N (m + 1)
  have hmn : m < n := lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _)
  have hmn' : (m : ℤ) < n := by exact_mod_cast hmn
  have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  have hdB := hB.curveSheafDegree_pos f hd
  have he := curveEulerCharacteristic_line_tensor f hd.le (hB.2.1.tensorPower n) hL
  rw [curveEulerCharacteristic_line_power f hd.le hB.2.1] at he
  have hp : 0 < curveEulerCharacteristic f (tensor L (tensorPower B n)) := by
    nlinarith
  have hh : 0 < Module.finrank k (ModuleScalarH f (tensor L (tensorPower B n)) 0) := by
    unfold curveEulerCharacteristic at hp
    omega
  exact ⟨n, by omega, hN n (le_max_left _ _) 0,
    exists_nonzero_section_of_h0_pos f _ hh⟩

include hd hB hL in
/-- A full effective divisor and an ample power recover every original line on the curve. -/
theorem exists_ample_twist_line_divisor :
    ∃ (n : ℕ) (I : X.IdealSheafData) (hI : EffectiveCartier I),
      0 < n ∧ IsFinite (I.subschemeι ≫ f) ∧
        Subsingleton (ModuleScalarH f (tensor L (tensorPower B n)) 1) ∧
        Nonempty (divisorLineBundle I hI ≅ tensor L (tensorPower B n)) ∧
        Nonempty (tensor (divisorLineBundle I hI) (moduleSheafDual (tensorPower B n)) ≅ L) := by
  obtain ⟨n, hn, hz, s, hs⟩ := exists_acyclic_line_twist_nonzero_section f hd hB hL
  let A := tensorPower B n
  have hA := hB.2.1.tensorPower n
  let I := lineSectionZeroIdeal (hL.tensor hA) s
  have hI := nonzero_lineSectionZeroIdeal_effectiveCartier (hL.tensor hA) s hs
  let e := nonzeroLineSectionZeroDivisorLineIso (hL.tensor hA) s hs
  refine ⟨n, I, hI, hn, hI.isFinite_of_integral_curve f hd.le, hz, ⟨e⟩, ⟨?_⟩⟩
  exact ModuleSheafTensor.congr e (Iso.refl _) ≪≫ associator L A (moduleSheafDual A) ≪≫
    ModuleSheafTensor.congr (Iso.refl L) (comm A _ ≪≫ lineSheafDualEvaluationIso hA) ≪≫
      rightUnitor L

end FLT.Mazur.FCurve
