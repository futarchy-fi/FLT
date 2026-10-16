/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedAdjacentRoots

/-!
# Full correction units agree across consecutive retained nodes

Both independent root constructions give the same whole Laurent correction on
the adjacent edge. The result also identifies the inverse squared correction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "E" => leftLaurentMap π
local notation "N" => retainedPrecedingEvaluation π
local notation "H3" => I.mul_mem_left π h3
local notation "H4" => I.mul_mem_left π h4
local notation "H6" => I.mul_mem_left (π ^ 2) h6
local notation "HS" => I.mul_mem_left π hs
local notation "L" => laurentArithmeticIdeal I
local notation "U" => retainedOppositeUnit W π s (π * c3) (π * c4) (π ^ 2 * c6)
  I hI ha hs h2 H3 H4 H6
local notation "U'" => retainedOppositeUnit W π (π * s) c3 c4 c6 I hI ha HS h2 h3 h4 h6
local notation "V" => retainedFactorCorrectionUnit W π s (π * c3) (π * c4) (π ^ 2 * c6)
  I hI ha hs h2 H3 H4 H6
local notation "V'" => retainedFactorCorrectionUnit W π (π * s) c3 c4 c6 I hI ha HS h2 h3 h4 h6

/-- The complete opposite factors agree along the original adjacent Laurent edge. -/
theorem retainedOppositeFactor_adjacent :
    E (retainedOppositeFactor W π s (π * c3) (π * c4) (π ^ 2 * c6)
      I hI ha hs h2 H3 H4 H6) =
    N (retainedOppositeFactor W π (π * s) c3 c4 c6 I hI ha HS h2 h3 h4 h6) := by
  unfold retainedOppositeFactor
  rw [map_add, map_add, map_add, map_add,
    retainedSlopeRoot_adjacent W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6,
    retainedConicRoot_adjacent W π c3 c4 c6 I hI ha h2 h3 h4 h6,
    retainedSlopeLinear_adjacent]

/-- The units built independently on consecutive nodes have identical entire edge restrictions. -/
theorem retainedOppositeUnit_adjacent :
    Units.map (E).toMonoidHom U = Units.map (N).toMonoidHom U' := by
  apply Units.ext
  change E (U : ChartRing π) = N (U' : ChartRing π)
  rw [retainedOppositeUnit_val, retainedOppositeUnit_val,
    retainedOppositeFactor_adjacent W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6]

/-- No term of the full squared correction changes at an adjacent retained boundary. -/
theorem retainedFactorCorrectionUnit_adjacent :
    Units.map (E).toMonoidHom V = Units.map (N).toMonoidHom V' := by
  unfold retainedFactorCorrectionUnit
  simp only [map_mul, map_pow, map_inv,
    retainedOppositeUnit_adjacent W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6]
  congr 2
  apply Units.ext
  change E (algebraMap R _ (zeroInitialTangentUnit W ha : R)) =
    N (algebraMap R _ (zeroInitialTangentUnit W ha : R))
  rw [AlgHom.commutes, AlgHom.commutes]

/-- The entire inverse correction also agrees, as required by the outgoing coordinate. -/
theorem retainedFactorCorrectionUnit_inv_adjacent :
    E (↑V⁻¹ : ChartRing π) = N (↑(V')⁻¹ : ChartRing π) :=
  congrArg (fun z : R[T;T⁻¹]ˣ ↦ (↑z⁻¹ : R[T;T⁻¹]))
    (retainedFactorCorrectionUnit_adjacent W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
