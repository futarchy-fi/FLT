/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainStep
public import FLT.Mazur.PolygonArithmeticTwoBranchRebaseNaturality

/-!
# Every retained-chain coefficient square survives a full correction

This is uniform in the correction index and in the integral error fields at every edge.
It retains the original quotient maps of each exact old and new smoothing.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonSmoothing PolygonScalingNaturality
open PolygonArithmeticSimultaneous
open LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (S : State R π n) (r : ℕ) (q : Edge n → Bool → R[T;T⁻¹]) (hS : S.Compatible)
local notation "A" => initialInput (π := π) r q
local notation "V" => retainedInput (π := π) r q
local notation "T" => terminalInput (π := π) r q

include hS

/-- The conjugated outgoing retained puncture retains its full coefficient square. -/
theorem State.outgoingFactor_compatible (i : Fin (n + 1)) (b : Bool) :
    CompatibleEquiv (fun m ↦ S.outgoingFactor r q m i b) := by
  intro m
  unfold State.outgoingFactor
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality _
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _ (hS.2.1 m i b) _ true
  · exact punctureEquiv_invert_naturality _

/-- All changed smoothings and every complete edge retain their coefficient squares. -/
theorem State.step_compatible : (S.step r q).Compatible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m b
    exact correctionSmoothing_restriction R π m _ _ (hS.1 m b) _
  · intro m i b
    exact twoBranchCorrectionSmoothing_restriction R π m _ _ (hS.2.1 m i b) _
  · intro m
    exact twoBranchCorrectionRebasedSmoothing_restriction R π m _ _ (hS.2.2.1 m) _
  · intro e b m
    cases e with
    | initial =>
      apply punctureEquiv_trans_naturality
      · apply punctureEquiv_trans_naturality
        · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
            (hS.2.1 m 0 b) _ false
        · exact hS.2.2.2 .initial b m
      · exact correctionPunctureFactor_symm_restriction R π m _ _ (hS.1 m b) _ true
    | incoming i =>
      apply punctureEquiv_trans_naturality
      · apply punctureEquiv_trans_naturality
        · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
            (hS.2.1 m i.succ b) _ false
        · exact hS.2.2.2 (.incoming i) b m
      · exact symm_naturality _ _ _ (S.outgoingFactor_compatible r q hS i.castSucc b m)
    | closing =>
      apply punctureEquiv_trans_naturality
      · apply punctureEquiv_trans_naturality
        · exact twoBranchCorrectionRebasedPunctureFactor_symm_restriction R π m _ _
            (hS.2.2.1 m) _ b
        · exact hS.2.2.2 .closing b m
      · exact symm_naturality _ _ _ (S.outgoingFactor_compatible r q hS (Fin.last n) b m)

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

/-- Both retained-node coordinates retain the quotient square of the same whole factor. -/
theorem State.retainedFactor_restriction (i : Fin (n + 1)) (b : Bool) :
    (ringMap f (S.retained (m + 1) i b) (S.retained m i b) (hS.2.1 m i b)).comp
        (S.retainedFactor r q (m + 1) i b).toRingHom =
      (S.retainedFactor r q m i b).toRingHom.comp
        (ringMap f ((N).retained (m + 1) i b) ((N).retained m i b) ((hN).2.1 m i b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _ (hS.2.1 m i b) (V i b)

/-- The common rebased terminal keeps its full old and new coefficient square. -/
theorem State.terminalFactor_restriction :
    (ringMap f ((N).terminal (m + 1)) ((N).terminal m) ((hN).2.2.1 m)).comp
        (S.terminalFactor r q (m + 1)).toRingHom =
      (S.terminalFactor r q m).toRingHom.comp
        (ringMap f (S.terminal (m + 1)) (S.terminal m) (hS.2.2.1 m)) :=
  twoBranchCorrectionRebasedFactor_restriction R π m _ _ (hS.2.2.1 m) T

end FLT.Mazur.PolygonArithmeticRetainedChain
