/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstAtlas

/-!
# Identify the installed depth-zero first factors

The initial open retains its original full inclusion. The unique last node uses
its changed smoothing, while the common terminal and infinity stay unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticZeroFirstAtlasChart
  arithmeticZeroFirstInitialIso arithmeticZeroFirstLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "ι" => arithmeticZeroFirstAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m 0 hj u hu
local notation "J" => arithmeticFourthOuterInitialZeroIdentification hπ data H m 0 hj u hu rfl
local notation "N" => arithmeticFourthOuterLastIdentification hπ data H m 0 hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "I" => arithmeticZeroFirstInitialIso hπ data H m 0 hj u hu
local notation "L" => arithmeticZeroFirstLastIso hπ data H m 0 hj u hu

/-- The installed initial comparison retains the original full open inclusion. -/
@[reassoc] theorem arithmeticZeroFirstInitial_chart (b : Bool) :
    (I b).hom ≫ ι (.initial b) = (J b).hom ≫ κ (.initial b) := by
  have h := arithmeticZeroFirstAtlasCorrection_chart hπ data H m hj u hu (.initial b)
  change ((J b).inv ≫ (I b).hom) ≫ ι (.initial b) = _ at h
  rw [Category.assoc] at h
  simpa only [Iso.hom_inv_id_assoc] using congrArg (fun f ↦ (J b).hom ≫ f) h

/-- The same full last factor retains the actual normalized inclusion on both branches. -/
@[reassoc] theorem arithmeticZeroFirstLast_chart (b : Bool) :
    (L b).hom ≫ ι (.retained ⟨0, by omega⟩ b) =
      (O b).hom ≫ (N b).hom ≫ κ (.retained ⟨0, by omega⟩ b) := by
  have h := arithmeticZeroFirstAtlasCorrection_chart hπ data H m hj u hu
    (.retained ⟨0, by omega⟩ b)
  change ((N b).inv ≫ (O b).inv ≫ (L b).hom) ≫
    ι (.retained ⟨0, by omega⟩ b) = _ at h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun f ↦ (O b).hom ≫ (N b).hom ≫ f) h

/-- Both closing edges keep the same entire common terminal inclusion. -/
theorem arithmeticZeroFirstAtlasChart_terminal : ι .terminal = κ .terminal := by
  simpa only [arithmeticZeroFirstAtlasCorrection, Iso.refl_hom, Category.id_comp] using
    arithmeticZeroFirstAtlasCorrection_chart hπ data H m hj u hu .terminal

/-- The full original infinity is unchanged by the depth-zero correction. -/
theorem arithmeticZeroFirstAtlasChart_infinity : ι .infinity = κ .infinity := by
  simpa only [arithmeticZeroFirstAtlasCorrection, Iso.refl_hom, Category.id_comp] using
    arithmeticZeroFirstAtlasCorrection_chart hπ data H m hj u hu .infinity

end FLT.Mazur.WeierstrassDividedDepth
