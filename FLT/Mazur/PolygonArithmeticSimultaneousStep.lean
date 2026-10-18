/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousSplit
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# A simultaneous correction step on the actual changing smoothings

The raw step is defined for arbitrary integral fields and every correction
index. Its full node factors start on the input state's actual smoothings.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R}
  (S : State R π) (r : ℕ) (q : Bool → Bool → R[T;T⁻¹])

/-- The scaled initial field in the arithmetic full-node convention. -/
def initialInput (b : Bool) : R[T;T⁻¹] := higherCorrectionField R π r (initialField q b)

/-- Both scaled fields for the same whole last node. -/
def lastInput (b a : Bool) : R[T;T⁻¹] := higherCorrectionField R π r (lastField q b a)

/-- The two scaled fields for the one common terminal. -/
def terminalInput (b : Bool) : R[T;T⁻¹] := higherCorrectionField R π r (terminalField q b)

local notation "A" => initialInput (π := π) r q
local notation "V" => lastInput (π := π) r q
local notation "T" => terminalInput (π := π) r q

/-- The outgoing puncture of the shared last factor in the closing coordinate. -/
def State.lastEdge (m : ℕ) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m (S.last m b) (V b) true)).trans invert

/-- Correct every actual node and both complete residuals simultaneously. -/
def State.step : State R π where
  initial m b := correctionSmoothing R π m (S.initial m b) (A b)
  last m b := twoBranchCorrectionSmoothing R π m (S.last m b) (V b)
  terminal m := twoBranchCorrectionRebasedSmoothing R π m (S.terminal m) T
  initialEquiv m b :=
    ((twoBranchCorrectionPunctureFactor R π m (S.last m b) (V b) false).trans
      (S.initialEquiv m b)).trans (correctionPunctureFactor R π m (S.initial m b) (A b) true).symm
  closingEquiv m b :=
    ((twoBranchCorrectionRebasedPunctureFactor R π m (S.terminal m) T b).symm.trans
      (S.closingEquiv m b)).trans (S.lastEdge r q m b).symm

/-- The full initial node comparison has the exact new and old smoothing rings. -/
def State.initialFactor (m : ℕ) (b : Bool) :
    ChartRing ((S.step r q).initial m b) ≃ₐ[Quotient R π m] ChartRing (S.initial m b) :=
  correctionNodeFactor R π m (S.initial m b) (A b)

/-- One whole last factor supplies both corrected edges. -/
def State.lastFactor (m : ℕ) (b : Bool) :
    ChartRing ((S.step r q).last m b) ≃ₐ[Quotient R π m] ChartRing (S.last m b) :=
  twoBranchCorrectionNodeFactor R π m (S.last m b) (V b)

/-- The inverse drift of both terminal fields is retained in one whole factor. -/
def State.terminalFactor (m : ℕ) :
    ChartRing (S.terminal m) ≃ₐ[Quotient R π m] ChartRing ((S.step r q).terminal m) :=
  twoBranchCorrectionRebasedFactor R π m (S.terminal m) T

/-- The exact incoming drift multiplies the entire preceding last smoothing. -/
theorem State.step_last (m : ℕ) (b : Bool) :
    (S.step r q).last m b =
      (1 - parameter R π m ^ (r + 1) * algebraMap R (Quotient R π m)
        ((q false b).coeff 1)) * S.last m b := by
  change twoBranchCorrectionSmoothing R π m (S.last m b) (V b) = _
  unfold twoBranchCorrectionSmoothing
  rw [lastInput, correctionSmoothing_higher, lastInput, correctionSmoothing_higher,
    lastField_outgoing_linear, map_zero, mul_zero, add_zero, one_mul, lastField_linear,
    map_neg, mul_neg, ← sub_eq_add_neg]

/-- Both initial punctures are supplied by the same full node factor. -/
theorem State.initialFactor_puncture (m : ℕ) (b c : Bool) :
    (punctureLaurentMap (S.initial m b) c).comp (S.initialFactor r q m b).toAlgHom =
      (correctionPunctureFactor R π m (S.initial m b) (A b) c).toAlgHom.comp
        (punctureLaurentMap ((S.step r q).initial m b) c) :=
  correctionNodeFactor_puncture R π m (S.initial m b) (A b) c

/-- Both last punctures are supplied by the same full two-branch factor. -/
theorem State.lastFactor_puncture (m : ℕ) (b c : Bool) :
    (punctureLaurentMap (S.last m b) c).comp (S.lastFactor r q m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (S.last m b) (V b) c).toAlgHom.comp
        (punctureLaurentMap ((S.step r q).last m b) c) :=
  twoBranchCorrectionNodeFactor_puncture R π m (S.last m b) (V b) c

/-- Both terminal punctures come from the common rebased node. -/
theorem State.terminalFactor_puncture (m : ℕ) (b : Bool) :
    (punctureLaurentMap ((S.step r q).terminal m) b).comp (S.terminalFactor r q m).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m (S.terminal m) T b).toAlgHom.comp
        (punctureLaurentMap (S.terminal m) b) :=
  twoBranchCorrectionRebasedFactor_puncture R π m (S.terminal m) T b

/-- Every smoothing retains its original annihilator after the complete step. -/
theorem State.step_annihilated (hS : S.Annihilated) : (S.step r q).Annihilated :=
  ⟨fun m b ↦ correctionSmoothing_annihilated R π m _ _ (hS.1 m b) _,
    (fun m b ↦ twoBranchCorrectionSmoothing_annihilated R π m _ _ (hS.2.1 m b) _),
    fun m ↦ twoBranchCorrectionRebasedSmoothing_annihilated R π m _ _ (hS.2.2 m) _⟩

end FLT.Mazur.PolygonArithmeticSimultaneous
