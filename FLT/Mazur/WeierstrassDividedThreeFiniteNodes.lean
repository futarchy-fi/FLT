/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFinitePunctures
public import FLT.Mazur.WeierstrassDividedThreeFiniteState

/-!
# Actual finite depth-three node comparisons

Specialize the constructed finite factors to the proved fifth seed. Each
comparison retains its exact source and target smoothing and both punctures.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticRetainedChain PolygonSmoothing
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 3 hj
local notation "S" => arithmeticThreeSeedState hπ data H hj u hu
local notation "hS" => arithmeticThreeSeedState_compatible hπ data H hj u hu
local notation "ha" => arithmeticThreeSeedState_annihilated hπ data H hj u hu
local notation "hr" => arithmeticThreeSeedState_normalized hπ data H hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m 3 hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m 3 hj
local notation "I" => arithmeticThreeFiniteState hπ data H hj u hu
variable (k m : ℕ)
local notation "Q" => Quotient R π m

/-- The full finite initial comparison starts on its exact accumulated smoothing. -/
def arithmeticThreeFiniteInitialFactor (b : Bool) :
    ChartRing ((I k).initial m b) ≃ₐ[Q] ChartRing ((S).initial m b) :=
  (S).iterateInitialFactor B hB hb hS ha 5 hr k m b

/-- Both full initial punctures along all further finite corrections. -/
def arithmeticThreeFiniteInitialPunctureEquiv (b c : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (S).iterateInitialPuncture B hB hb hS ha 5 hr m b c k

/-- Both finite initial substitutions are induced by the same full node factor. -/
theorem arithmeticThreeFiniteInitialFactor_puncture (b c : Bool) :
    (punctureLaurentMap ((S).initial m b) c).comp
        (arithmeticThreeFiniteInitialFactor hπ data H hj u hu k m b).toAlgHom =
      (arithmeticThreeFiniteInitialPunctureEquiv hπ data H hj u hu k m b c).toAlgHom.comp
        (punctureLaurentMap ((I k).initial m b) c) :=
  (S).iterateInitialFactor_puncture B hB hb hS ha 5 hr k m b c

/-- The full finite retained comparison starts on its exact accumulated smoothing. -/
def arithmeticThreeFiniteRetainedFactor (i : Fin 4) (b : Bool) :
    ChartRing ((I k).retained m i b) ≃ₐ[Q] ChartRing ((S).retained m i b) :=
  (S).iterateRetainedFactor B hB hb hS ha 5 hr k m i b

/-- Both full retained punctures along all further finite corrections. -/
def arithmeticThreeFiniteRetainedPunctureEquiv (i : Fin 4) (b c : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (S).iterateRetainedPuncture B hB hb hS ha 5 hr m i b c k

/-- Both finite retained substitutions are induced by the same full node factor. -/
theorem arithmeticThreeFiniteRetainedFactor_puncture (i : Fin 4) (b c : Bool) :
    (punctureLaurentMap ((S).retained m i b) c).comp
        (arithmeticThreeFiniteRetainedFactor hπ data H hj u hu k m i b).toAlgHom =
      (arithmeticThreeFiniteRetainedPunctureEquiv hπ data H hj u hu k m i b c).toAlgHom.comp
        (punctureLaurentMap ((I k).retained m i b) c) :=
  (S).iterateRetainedFactor_puncture B hB hb hS ha 5 hr k m i b c

/-- The common terminal comparison keeps its complete inverse smoothing drift. -/
def arithmeticThreeFiniteTerminalFactor :
    ChartRing ((S).terminal m) ≃ₐ[Q] ChartRing ((I k).terminal m) :=
  (S).iterateTerminalFactor B hB hb hS ha 5 hr k m

/-- Both common terminal substitutions along every finite rebasing step. -/
def arithmeticThreeFiniteTerminalPunctureEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (S).iterateTerminalPuncture B hB hb hS ha 5 hr m b k

/-- Both terminal punctures are supplied by the actual common terminal comparison. -/
theorem arithmeticThreeFiniteTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap ((I k).terminal m) b).comp
        (arithmeticThreeFiniteTerminalFactor hπ data H hj u hu k m).toAlgHom =
      (arithmeticThreeFiniteTerminalPunctureEquiv hπ data H hj u hu k m b).toAlgHom.comp
        (punctureLaurentMap ((S).terminal m) b) :=
  (S).iterateTerminalFactor_puncture B hB hb hS ha 5 hr k m b

end FLT.Mazur.WeierstrassDividedDepth
