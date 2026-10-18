/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousStep
public import FLT.Mazur.PolygonArithmeticTwoBranchRebaseNaturality

/-!
# Every coefficient square survives the simultaneous changing-smoothing step

This is uniform in the correction index and in the two integral error fields.
It retains the original quotient maps of each exact old and new smoothing.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonSmoothing PolygonScalingNaturality
open LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R}
  (S : State R π) (r : ℕ) (q : Bool → Bool → R[T;T⁻¹]) (hS : S.Compatible)
local notation "A" => initialInput (π := π) r q
local notation "V" => lastInput (π := π) r q
local notation "T" => terminalInput (π := π) r q

include hS

/-- The conjugated outgoing last puncture retains its full coefficient square. -/
theorem State.lastEdge_compatible (b : Bool) :
    CompatibleEquiv (fun m ↦ S.lastEdge r q m b) := by
  intro m
  unfold State.lastEdge
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality _
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _ (hS.2.1 m b) _ true
  · exact punctureEquiv_invert_naturality _

/-- Both changed scalar systems and both complete edge maps remain compatible. -/
theorem State.step_compatible : (S.step r q).Compatible := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m b
    exact correctionSmoothing_restriction R π m _ _ (hS.1 m b) _
  · intro m b
    exact twoBranchCorrectionSmoothing_restriction R π m _ _ (hS.2.1 m b) _
  · intro m
    exact twoBranchCorrectionRebasedSmoothing_restriction R π m _ _ (hS.2.2.1 m) _
  · intro b m
    apply punctureEquiv_trans_naturality
    · apply punctureEquiv_trans_naturality
      · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _ (hS.2.1 m b) _ false
      · exact hS.2.2.2.1 b m
    · exact correctionPunctureFactor_symm_restriction R π m _ _ (hS.1 m b) _ true
  · intro b m
    apply punctureEquiv_trans_naturality
    · apply punctureEquiv_trans_naturality
      · exact twoBranchCorrectionRebasedPunctureFactor_symm_restriction R π m _ _
          (hS.2.2.1 m) _ b
      · exact hS.2.2.2.2 b m
    · exact symm_naturality _ _ _ (S.lastEdge_compatible r q hS b m)

variable (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "N" => S.step r q
local notation "hN" => S.step_compatible r q hS

/-- The full initial-node factor respects the exact old and new smoothing quotients. -/
theorem State.initialFactor_restriction (b : Bool) :
    (ringMap f (S.initial (m + 1) b) (S.initial m b) (hS.1 m b)).comp
        (S.initialFactor r q (m + 1) b).toRingHom =
      (S.initialFactor r q m b).toRingHom.comp
        (ringMap f ((N).initial (m + 1) b) ((N).initial m b) ((hN).1 m b)) :=
  correctionNodeFactor_restriction R π m _ _ (hS.1 m b) (A b)

/-- Both last-node coordinates retain the quotient square of the same whole factor. -/
theorem State.lastFactor_restriction (b : Bool) :
    (ringMap f (S.last (m + 1) b) (S.last m b) (hS.2.1 m b)).comp
        (S.lastFactor r q (m + 1) b).toRingHom =
      (S.lastFactor r q m b).toRingHom.comp
        (ringMap f ((N).last (m + 1) b) ((N).last m b) ((hN).2.1 m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _ (hS.2.1 m b) (V b)

/-- The common rebased terminal keeps its full old and new coefficient square. -/
theorem State.terminalFactor_restriction :
    (ringMap f ((N).terminal (m + 1)) ((N).terminal m) ((hN).2.2.1 m)).comp
        (S.terminalFactor r q (m + 1)).toRingHom =
      (S.terminalFactor r q m).toRingHom.comp
        (ringMap f (S.terminal (m + 1)) (S.terminal m) (hS.2.2.1 m)) :=
  twoBranchCorrectionRebasedFactor_restriction R π m _ _ (hS.2.2.1 m) T

end FLT.Mazur.PolygonArithmeticSimultaneous
