/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerFrameComparison
public import FLT.Mazur.SectionPoleMultiplicativeCoordinates
public import FLT.Mazur.SectionPoleAdaptedBasis

/-!
# Changing the frame in the original pole splitting

The splitting is chosen before the leading frame. Changing that frame
therefore scales its normalized lift by the exact tensor power of the line
transition unit, with no lower-pole correction on this fixed family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback
variable {X S : Scheme} (s : S ⟶ X) (hI : EffectiveCartier s.ker)
  (e f : (pullback s).obj (divisorLineBundle s.ker hI) ≅ structureModule S)

/-- The leading-line coordinates change by the power of the actual line transition. -/
theorem sectionPoleMultiplicativeCoordinates_change (n : ℕ)
    (z : Γ(sectionPoleLine s hI n, ⊤)) :
    sectionPoleMultiplicativeCoordinates s hI e n z =
      (frameComparisonUnit e f ⊤ : Γ(S, ⊤)) ^ n *
        sectionPoleMultiplicativeCoordinates s hI f n z := by
  change (tensorPowerTrivialization e n).hom.app ⊤
    ((tensorPowerIso s (divisorLineBundle s.ker hI) n).hom.app ⊤ z) = _
  exact tensorPowerFrameComparison_apply e f n _

/-- The normalized leading vector retains the same exact transition power. -/
theorem sectionPoleMultiplicativeCoordinates_symm_change (n : ℕ) :
    (sectionPoleMultiplicativeCoordinates s hI f n).symm 1 =
      (frameComparisonUnit e f ⊤ : Γ(S, ⊤)) ^ n •
        (sectionPoleMultiplicativeCoordinates s hI e n).symm 1 := by
  apply (sectionPoleMultiplicativeCoordinates s hI e n).injective
  rw [sectionPoleMultiplicativeCoordinates_change s hI e f n,
    LinearEquiv.apply_symm_apply, mul_one, _root_.map_smul,
    LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

variable [IsAffine S] (p : X ⟶ S) [IsSeparated p] (hs : s ≫ p = 𝟙 S)
  (m : ℕ) [Subsingleton (ModuleH (tensorPower (divisorLineBundle s.ker hI) m) 1)]

/-- Changing only the original frame scales the lift in the fixed original splitting. -/
theorem sectionPoleNormalizedLift_frameChange :
    sectionPoleNormalizedLift p s hs hI m
      (sectionPoleMultiplicativeCoordinates s hI f (m + 1)) =
    (frameComparisonUnit e f ⊤ : Γ(S, ⊤)) ^ (m + 1) •
      sectionPoleNormalizedLift p s hs hI m
        (sectionPoleMultiplicativeCoordinates s hI e (m + 1)) := by
  unfold sectionPoleNormalizedLift
  rw [sectionPoleMultiplicativeCoordinates_symm_change s hI e f,
    ← _root_.map_smul (sectionPoleSplit p s hs hI m).val.symm]
  rw [Prod.smul_mk, smul_zero]

end FLT.Mazur.FCurve
