/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstAtlasCoordinates
public import FLT.Mazur.WeierstrassDividedGlobalRegularLift

/-!
# Actual lifts for unit-center members of the complete successor atlas

A proved unit output center constructs the whole successor action map on
that member. Its uniqueness holds after every affine restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)

local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstDividedAffineCover hπ data hn

local notation "D" => firstDividedInputCover hπ data hn
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
/-- Construct the whole successor lift from a proved unit output center. -/
def firstDividedUnitAction (i : (U).I₀)
    (hi : (I).map (firstDividedAlpha hπ data hn i) = ⊤) :
    Spec ((U).X i) ⟶ finiteGlobalModel hπ data 1 hn :=
  finiteGlobalRegularLift hπ data 0 hn (firstDividedAlpha hπ data hn i) 1
    (hi.trans Ideal.span_singleton_one.symm) isRegular_one

/-- The actual local lift has exactly the normalized output of its simultaneous domain. -/
@[reassoc] theorem firstDividedUnitAction_step (i : (U).I₀)
    (hi : (I).map (firstDividedAlpha hπ data hn i) = ⊤) :
    firstDividedUnitAction hπ data hn i hi ≫ finiteGlobalStep hπ data 0 hn =
      (U).f i ≫ pullback.snd _ _ ≫ v := by
  rw [firstDividedUnitAction, finiteGlobalRegularLift_step, firstDividedAlpha_spec,
    Category.assoc]

/-- Unit-center lifts contract to the existing action on their entire source member. -/
@[reassoc] theorem firstDividedUnitAction_output (i : (U).I₀)
    (hi : (I).map (firstDividedAlpha hπ data hn i) = ⊤) :
    firstDividedUnitAction hπ data hn i hi ≫ finiteGlobalStep hπ data 0 hn =
      (U).f i ≫ pullback.fst _ _ ≫ firstActionOutput hπ data hn := by
  rw [firstDividedUnitAction_step, ← pullback.condition]

/-- Every affine restriction preserves uniqueness, with no flatness requirement. -/
theorem firstDividedUnitAction_affine_unique (i : (U).I₀)
    (hi : (I).map (firstDividedAlpha hπ data hn i) = ⊤)
    {S : Type u} [CommRing S] (p : Spec (.of S) ⟶ Spec ((U).X i))
    (b : Spec (.of S) ⟶ finiteGlobalModel hπ data 1 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstDividedUnitAction hπ data hn i hi ≫ finiteGlobalStep hπ data 0 hn) :
    b = p ≫ firstDividedUnitAction hπ data hn i hi := by
  let ψ := affineChartRingHom p
  have hψ : Spec.map (CommRingCat.ofHom ψ) = p := affineChartRingHom_spec _
  have hI : (I).map (ψ.comp (firstDividedAlpha hπ data hn i)) = Ideal.span {1} := by
    rw [← Ideal.map_map, hi, Ideal.map_top, Ideal.span_singleton_one]
  have he : (p ≫ firstDividedUnitAction hπ data hn i hi) ≫
      finiteGlobalStep hπ data 0 hn =
      Spec.map (CommRingCat.ofHom (ψ.comp (firstDividedAlpha hπ data hn i))) ≫ v := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ, Category.assoc,
      firstDividedUnitAction_step, firstDividedAlpha_spec]
    simp only [Category.assoc]
  exact finiteGlobalStep_regular_center_ext hπ data 0 hn _ 1 hI isRegular_one
    b _ (hb.trans ((Category.assoc _ _ _).symm.trans he)) he

end FLT.Mazur.WeierstrassDividedDepth
