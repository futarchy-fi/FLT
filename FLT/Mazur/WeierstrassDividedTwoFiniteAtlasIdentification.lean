/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlas
public import FLT.Mazur.WeierstrassDividedTwoSeedOrientation

/-!
# Full finite chart comparisons at all three depth-two retained labels

The last label keeps its seed orientation through the entire finite factor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowAtlasChart arithmeticTwoFiniteInitialIso arithmeticTwoFiniteRetainedIso
  arithmeticTwoFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticTwoFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "C" => arithmeticTwoFiniteRetainedIso hπ data H k m hj u hu

/-- The first retained chart recovers its complete fifth inclusion. -/
@[reassoc] theorem arithmeticTwoFiniteFirst_chart (b : Bool) :
    (C 0 b).hom ≫ ι (.retained 0 b) = κ (.retained 0 b) :=
  arithmeticTwoFiniteAtlasCorrection_chart hπ data H k m hj u hu _

/-- The middle predecessor recovers its complete fifth inclusion. -/
@[reassoc] theorem arithmeticTwoFiniteMiddle_chart (b : Bool) :
    (C 1 b).hom ≫ ι (.retained 1 b) = κ (.retained 1 b) :=
  arithmeticTwoFiniteAtlasCorrection_chart hπ data H k m hj u hu _

/-- The last retained chart recovers its oriented fifth inclusion. -/
@[reassoc] theorem arithmeticTwoFiniteLast_chart (b : Bool) :
    (C 2 b).hom ≫ ι (.retained 2 b) = arithmeticTwoSeedLastChart hπ data H m hj u hu b := by
  have h := arithmeticTwoFiniteAtlasCorrection_chart hπ data H k m hj u hu (.retained 2 b)
  change ((twistedRetainedOrientation data H m b).inv ≫ (C 2 b).hom) ≫ _ = _ at h
  apply (cancel_epi (twistedRetainedOrientation data H m b).inv).mp
  simp only [arithmeticTwoSeedLastChart, Iso.inv_hom_id_assoc]
  change _ = κ (.retained (2 : Fin 3) b)
  simpa only [Category.assoc] using h

/-- The complete finite correction leaves the infinity chart and its map unchanged. -/
theorem arithmeticTwoFiniteAtlasChart_infinity : ι .infinity = κ .infinity := by
  simp only [arithmeticTwoFiniteAtlasChart, arithmeticTwoFiniteAtlasCorrection, Iso.refl_inv]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
