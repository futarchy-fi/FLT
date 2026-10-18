/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicStep

/-!
# Full quotient squares for a cyclic correction

All nodes and edges use the original coefficient restrictions. The same
whole-node factors supply both punctures and their exact quotient squares.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (q : ι → R[T;T⁻¹]) (S : State R π ι) (r : ℕ)
  (hS : S.Compatible)

include hS

/-- Both full puncture substitutions commute with the actual arithmetic quotients. -/
theorem State.punctureFactor_compatible (i : ι) (a : Bool) :
    CompatibleEquiv (fun m ↦ S.punctureFactor σ q r m i a) := by
  intro m
  exact twoBranchCorrectionPunctureFactor_restriction R π m _ _ (hS.1 m i) _ a

/-- The complete cyclic step preserves every smoothing and edge coefficient square. -/
theorem State.step_compatible : (S.step σ q r).Compatible := by
  constructor
  · intro m i
    exact twoBranchCorrectionSmoothing_restriction R π m _ _ (hS.1 m i) _
  · intro i m
    apply punctureEquiv_trans_naturality
    · apply punctureEquiv_trans_naturality
      · exact S.punctureFactor_compatible σ q r hS (σ i) false m
      · exact hS.2 i m
    · exact symm_naturality _ _ _ (S.punctureFactor_compatible σ q r hS i true m)

/-- Every full node correction, including both coordinates, has its original quotient square. -/
theorem State.nodeFactor_restriction (m : ℕ) (i : ι) :
    (ringMap (restriction R π m).toRingHom (S.parameter (m + 1) i)
        (S.parameter m i) (hS.1 m i)).comp (S.nodeFactor σ q r (m + 1) i).toRingHom =
      (S.nodeFactor σ q r m i).toRingHom.comp
        (ringMap (restriction R π m).toRingHom ((S.step σ q r).parameter (m + 1) i)
          ((S.step σ q r).parameter m i) ((S.step_compatible σ q r hS).1 m i)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _ (hS.1 m i) _

end FLT.Mazur.PolygonArithmeticCyclic
