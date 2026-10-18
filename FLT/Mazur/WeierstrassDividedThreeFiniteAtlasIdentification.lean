/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlas
public import FLT.Mazur.WeierstrassDividedThreeSeedOrientation

/-!
# Full finite chart comparisons at all four depth-three retained labels

The last label keeps its seed orientation through the entire finite factor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThreeSeedAtlasChart arithmeticThreeFiniteInitialIso arithmeticThreeFiniteRetainedIso
  arithmeticThreeFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticThreeFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticThreeSeedAtlasChart hπ data H m hj u hu
local notation "C" => arithmeticThreeFiniteRetainedIso hπ data H k m hj u hu

/-- Every retained full factor recovers its identified and oriented seed inclusion. -/
@[reassoc] theorem arithmeticThreeFiniteRetained_chart (i : Fin 4) (b : Bool) :
    (C i b).hom ≫ ι (.retained i b) = κ (.retained i b) :=
  arithmeticThreeFiniteAtlasCorrection_chart hπ data H k m hj u hu _

/-- The complete finite correction leaves the infinity chart and its map unchanged. -/
theorem arithmeticThreeFiniteAtlasChart_infinity : ι .infinity = κ .infinity := by
  simp only [arithmeticThreeFiniteAtlasChart, arithmeticThreeFiniteAtlasCorrection, Iso.refl_inv]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
