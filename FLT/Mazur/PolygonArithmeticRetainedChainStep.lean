/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainSplit
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# One simultaneous correction of the entire retained chain

Every retained node has one whole two-branch factor. Its two punctures correct
its two incident edges, while the common terminal retains both inverse drifts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (S : State R π n) (r : ℕ) (q : Edge n → Bool → R[T;T⁻¹])

/-- The initial full-node input at the chosen correction order. -/
def initialInput (b : Bool) : R[T;T⁻¹] := higherCorrectionField R π r (initialField q b)

/-- Both inputs at each retained node use its actual two incident edges. -/
def retainedInput (i : Fin (n + 1)) (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π r (retainedField q i b a)

/-- Both closing fields act on the same terminal. -/
def terminalInput (b : Bool) : R[T;T⁻¹] := higherCorrectionField R π r (terminalField q b)

local notation "A" => initialInput (π := π) r q
local notation "V" => retainedInput (π := π) r q
local notation "T" => terminalInput (π := π) r q

/-- The outgoing retained puncture in the common edge coordinate. -/
def State.outgoingFactor (m : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (invert.trans
    (twoBranchCorrectionPunctureFactor R π m (S.retained m i b) (V i b) true)).trans invert

/-- Correct all smoothings and every complete edge with shared whole-node factors. -/
def State.step : State R π n where
  initial m b := correctionSmoothing R π m (S.initial m b) (A b)
  retained m i b := twoBranchCorrectionSmoothing R π m (S.retained m i b) (V i b)
  terminal m := twoBranchCorrectionRebasedSmoothing R π m (S.terminal m) T
  edgeEquiv
    | .initial, m, b =>
      ((twoBranchCorrectionPunctureFactor R π m (S.retained m 0 b) (V 0 b) false).trans
        (S.edgeEquiv .initial m b)).trans
          (correctionPunctureFactor R π m (S.initial m b) (A b) true).symm
    | .incoming i, m, b =>
      ((twoBranchCorrectionPunctureFactor R π m
        (S.retained m i.succ b) (V i.succ b) false).trans
          (S.edgeEquiv (.incoming i) m b)).trans (S.outgoingFactor r q m i.castSucc b).symm
    | .closing, m, b =>
      ((twoBranchCorrectionRebasedPunctureFactor R π m (S.terminal m) T b).symm.trans
        (S.edgeEquiv .closing m b)).trans (S.outgoingFactor r q m (Fin.last n) b).symm

/-- The initial factor compares the actual changed and original smoothing rings. -/
def State.initialFactor (m : ℕ) (b : Bool) :
    ChartRing ((S.step r q).initial m b) ≃ₐ[Quotient R π m] ChartRing (S.initial m b) :=
  correctionNodeFactor R π m (S.initial m b) (A b)

/-- One whole factor at each retained node serves both neighboring edges. -/
def State.retainedFactor (m : ℕ) (i : Fin (n + 1)) (b : Bool) :
    ChartRing ((S.step r q).retained m i b) ≃ₐ[Quotient R π m]
      ChartRing (S.retained m i b) :=
  twoBranchCorrectionNodeFactor R π m (S.retained m i b) (V i b)

/-- The terminal comparison retains both inverse smoothing drifts. -/
def State.terminalFactor (m : ℕ) :
    ChartRing (S.terminal m) ≃ₐ[Quotient R π m] ChartRing ((S.step r q).terminal m) :=
  twoBranchCorrectionRebasedFactor R π m (S.terminal m) T

/-- The full incoming linear drift multiplies each entire preceding retained smoothing. -/
theorem State.step_retained (m : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (S.step r q).retained m i b =
      (1 - parameter R π m ^ (r + 1) * algebraMap R (Quotient R π m)
        ((q (incomingEdge i) b).coeff 1)) * S.retained m i b := by
  change twoBranchCorrectionSmoothing R π m (S.retained m i b) (V i b) = _
  unfold twoBranchCorrectionSmoothing
  rw [retainedInput, correctionSmoothing_higher, retainedInput, correctionSmoothing_higher,
    retainedField_outgoing_linear, map_zero, mul_zero, add_zero, one_mul,
    retainedField_linear, map_neg, mul_neg, ← sub_eq_add_neg]

/-- Both initial punctures are induced by the same whole-node factor. -/
theorem State.initialFactor_puncture (m : ℕ) (b c : Bool) :
    (punctureLaurentMap (S.initial m b) c).comp (S.initialFactor r q m b).toAlgHom =
      (correctionPunctureFactor R π m (S.initial m b) (A b) c).toAlgHom.comp
        (punctureLaurentMap ((S.step r q).initial m b) c) :=
  correctionNodeFactor_puncture R π m (S.initial m b) (A b) c

/-- Both retained punctures come from the same complete factor on the same smoothing. -/
theorem State.retainedFactor_puncture (m : ℕ) (i : Fin (n + 1)) (b c : Bool) :
    (punctureLaurentMap (S.retained m i b) c).comp (S.retainedFactor r q m i b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (S.retained m i b) (V i b) c).toAlgHom.comp
        (punctureLaurentMap ((S.step r q).retained m i b) c) :=
  twoBranchCorrectionNodeFactor_puncture R π m (S.retained m i b) (V i b) c

/-- Both closing corrections come from the common terminal factor. -/
theorem State.terminalFactor_puncture (m : ℕ) (b : Bool) :
    (punctureLaurentMap ((S.step r q).terminal m) b).comp (S.terminalFactor r q m).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m (S.terminal m) T b).toAlgHom.comp
        (punctureLaurentMap (S.terminal m) b) :=
  twoBranchCorrectionRebasedFactor_puncture R π m (S.terminal m) T b

/-- Every actual smoothing keeps its original top-power annihilator. -/
theorem State.step_annihilated (hS : S.Annihilated) : (S.step r q).Annihilated :=
  ⟨fun m b ↦ correctionSmoothing_annihilated R π m _ _ (hS.1 m b) _,
    (fun m i b ↦ twoBranchCorrectionSmoothing_annihilated R π m _ _ (hS.2.1 m i b) _),
    fun m ↦ twoBranchCorrectionRebasedSmoothing_annihilated R π m _ _ (hS.2.2 m) _⟩

end FLT.Mazur.PolygonArithmeticRetainedChain
