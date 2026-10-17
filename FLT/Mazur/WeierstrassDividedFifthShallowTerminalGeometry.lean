/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowJointGeometry
public import FLT.Mazur.WeierstrassDividedFourthTerminalGeometry

/-!
# Full terminal punctures and quotient square for the fifth depth-two correction

The inverse geometric factor retains all earlier scalar drifts, the new
rebasing, and the original arithmetic coefficient restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu
local notation "T" => arithmeticFifthShallowTerminalSmoothing hπ data H j hj u hu
local notation "V" => arithmeticFifthShallowTerminalIntegralField hπ data H j hj u hu
local notation "F" => fun k ↦ arithmeticFifthShallowTerminalIso hπ data H k j hj u hu

/-- Both inverse terminal substitutions come from the same full rebased node. -/
@[reassoc] theorem arithmeticFifthShallowTerminalIso_puncture (b : Bool) :
    punctureOpen (t m) b ≫ (F m).hom =
      (punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m (t m) V b).symm).hom ≫
        punctureOpen (T m) b := by
  unfold arithmeticFifthShallowTerminalIso arithmeticFifthShallowTerminalSmoothing
    arithmeticFifthShallowTerminalFactor
  exact punctureFactor_spec _ _
    (twoBranchCorrectionRebasedFactor R π m (t m) V).symm
    (twoBranchCorrectionRebasedPunctureFactor R π m (t m) V b).symm b
    (twoBranchCorrectionRebasedFactor_symm_puncture R π m (t m) V b)

/-- The terminal coefficient map keeps its exact fifth smoothing. -/
def arithmeticFifthShallowTerminalRestriction :
    PolygonSmoothing.chart (Quotient R π m) (T m) ⟶
      PolygonSmoothing.chart (Quotient R π (m + 1)) (T (m + 1)) :=
  Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom _ _
    (arithmeticFifthShallowTerminalSmoothing_restriction hπ data H j hj u hu m)))

/-- The geometric inverse has the full square on the actual fourth corrected old terminal. -/
@[reassoc] theorem arithmeticFifthShallowTerminalIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap (restriction R π m).toRingHom (t (m + 1)) (t m)
        (arithmeticFourthTerminalSmoothing_restriction hπ data H j hj u hu m))) ≫
      (F (m + 1)).hom =
        (F m).hom ≫ arithmeticFifthShallowTerminalRestriction hπ data H j hj u hu m := by
  apply (cancel_epi (F m).inv).mp
  apply (cancel_mono (F (m + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact (nodeFactorIso_restriction _ _ _ _ _ _ _ _ _
    (arithmeticFifthShallowTerminalFactor_restriction hπ data H j hj u hu m)).symm

end FLT.Mazur.WeierstrassDividedDepth
