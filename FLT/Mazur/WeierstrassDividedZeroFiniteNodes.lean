/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousFinitePunctures
public import FLT.Mazur.WeierstrassDividedZeroFiniteState

/-!
# Actual finite depth-zero node comparisons

Specialize the constructed finite factors to the proved fifth seed. Each
comparison retains its exact source and target smoothing and both punctures.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m j hj
local notation "S" => arithmeticZeroFifthState hπ data H j hj u hu
local notation "hS" => arithmeticZeroFifthState_compatible hπ data H j hj u hu
local notation "ha" => arithmeticZeroFifthState_annihilated hπ data H j hj u hu
local notation "hr" => arithmeticZeroFifthState_normalized hπ data H j hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m j hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m j hj
local notation "I" => arithmeticZeroFiniteState hπ data H j hj u hu
variable (k m : ℕ)
local notation "Q" => Quotient R π m

/-- The full finite initial comparison starts on its exact accumulated smoothing. -/
def arithmeticZeroFiniteInitialFactor (b : Bool) :
    ChartRing ((I k).initial m b) ≃ₐ[Q] ChartRing ((S).initial m b) :=
  (S).iterateInitialFactor B hB hb hS ha 5 hr k m b

/-- Both full initial punctures along all further finite corrections. -/
def arithmeticZeroFiniteInitialPunctureEquiv (b c : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (S).iterateInitialPuncture B hB hb hS ha 5 hr m b c k

/-- Both finite initial substitutions are induced by the same full node factor. -/
theorem arithmeticZeroFiniteInitialFactor_puncture (b c : Bool) :
    (punctureLaurentMap ((S).initial m b) c).comp
        (arithmeticZeroFiniteInitialFactor hπ data H j hj u hu k m b).toAlgHom =
      (arithmeticZeroFiniteInitialPunctureEquiv hπ data H j hj u hu k m b c).toAlgHom.comp
        (punctureLaurentMap ((I k).initial m b) c) :=
  (S).iterateInitialFactor_puncture B hB hb hS ha 5 hr k m b c

/-- The full finite last comparison starts on its exact accumulated smoothing. -/
def arithmeticZeroFiniteLastFactor (b : Bool) :
    ChartRing ((I k).last m b) ≃ₐ[Q] ChartRing ((S).last m b) :=
  (S).iterateLastFactor B hB hb hS ha 5 hr k m b

/-- Both full last punctures along all further finite corrections. -/
def arithmeticZeroFiniteLastPunctureEquiv (b c : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (S).iterateLastPuncture B hB hb hS ha 5 hr m b c k

/-- Both finite last substitutions are induced by the same full node factor. -/
theorem arithmeticZeroFiniteLastFactor_puncture (b c : Bool) :
    (punctureLaurentMap ((S).last m b) c).comp
        (arithmeticZeroFiniteLastFactor hπ data H j hj u hu k m b).toAlgHom =
      (arithmeticZeroFiniteLastPunctureEquiv hπ data H j hj u hu k m b c).toAlgHom.comp
        (punctureLaurentMap ((I k).last m b) c) :=
  (S).iterateLastFactor_puncture B hB hb hS ha 5 hr k m b c

/-- The common terminal comparison keeps its complete inverse smoothing drift. -/
def arithmeticZeroFiniteTerminalFactor :
    ChartRing ((S).terminal m) ≃ₐ[Q] ChartRing ((I k).terminal m) :=
  (S).iterateTerminalFactor B hB hb hS ha 5 hr k m

/-- Both common terminal substitutions along every finite rebasing step. -/
def arithmeticZeroFiniteTerminalPunctureEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (S).iterateTerminalPuncture B hB hb hS ha 5 hr m b k

/-- Both terminal punctures are supplied by the actual common terminal comparison. -/
theorem arithmeticZeroFiniteTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap ((I k).terminal m) b).comp
        (arithmeticZeroFiniteTerminalFactor hπ data H j hj u hu k m).toAlgHom =
      (arithmeticZeroFiniteTerminalPunctureEquiv hπ data H j hj u hu k m b).toAlgHom.comp
        (punctureLaurentMap ((S).terminal m) b) :=
  (S).iterateTerminalFactor_puncture B hB hb hS ha 5 hr k m b

end FLT.Mazur.WeierstrassDividedDepth
