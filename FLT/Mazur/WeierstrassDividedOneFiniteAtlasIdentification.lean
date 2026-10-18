/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteAtlas
public import FLT.Mazur.WeierstrassDividedOneSeedOrientation

/-!
# Full finite chart comparisons at both depth-one retained labels

The last label keeps its seed orientation through the entire finite factor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthInitialAtlasChart arithmeticOneFiniteInitialIso arithmeticOneFiniteRetainedIso
  arithmeticOneFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticOneFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "C" => arithmeticOneFiniteRetainedIso hπ data H k m hj u hu

/-- The first retained chart recovers its complete fifth inclusion. -/
@[reassoc] theorem arithmeticOneFiniteFirst_chart (b : Bool) :
    (C 0 b).hom ≫ ι (.retained 0 b) = κ (.retained 0 b) :=
  arithmeticOneFiniteAtlasCorrection_chart hπ data H k m hj u hu _

/-- The last retained chart recovers its oriented fifth inclusion. -/
@[reassoc] theorem arithmeticOneFiniteLast_chart (b : Bool) :
    (C 1 b).hom ≫ ι (.retained 1 b) = arithmeticOneSeedLastChart hπ data H m hj u hu b := by
  have h := arithmeticOneFiniteAtlasCorrection_chart hπ data H k m hj u hu (.retained 1 b)
  change ((twistedRetainedOrientation data H m b).inv ≫ (C 1 b).hom) ≫ _ = _ at h
  apply (cancel_epi (twistedRetainedOrientation data H m b).inv).mp
  simp only [arithmeticOneSeedLastChart, Iso.inv_hom_id_assoc]
  change _ = κ (.retained (1 : Fin 2) b)
  simpa only [Category.assoc] using h

/-- The complete finite correction leaves the infinity chart and its map unchanged. -/
theorem arithmeticOneFiniteAtlasChart_infinity : ι .infinity = κ .infinity := by
  simp only [arithmeticOneFiniteAtlasChart, arithmeticOneFiniteAtlasCorrection, Iso.refl_inv]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
