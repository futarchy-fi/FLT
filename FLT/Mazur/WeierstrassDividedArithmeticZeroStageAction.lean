/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasOriginalAction
public import FLT.Mazur.WeierstrassDividedOriginalChartContractions

/-!
# All arithmetic smooth chart pairs at final stage zero

Every stage-zero chart is an unchanged open of the original cubic. Thus all
nine ordered chart pairs have full quotient-valued action outputs, including
the terminal diagonal. No positive node depth is required.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  globalTensorAtlasObject arithmeticTensorAtlasMap tensorIntegralAtlasProjection
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))

/-- Every one of the three stage-zero charts contracts by an open immersion. -/
instance globalZeroStageOriginalContraction_open (a : Fin 3) :
    IsOpenImmersion (globalIntegralAtlasMap hπ data 0 (Nat.zero_le n) a ≫
      finiteGlobalContraction hπ data 0 (Nat.zero_le n)) := by
  fin_cases a
  · exact globalInfinityOriginalContraction_open hπ data 0 (Nat.zero_le n)
  · exact globalZeroTerminalOriginalContraction_open hπ data
  · exact globalInitialOriginalContraction_open hπ 0 (Nat.zero_le n) data

variable [IsNoetherianRing R] (m : ℕ) (a b : Fin 3)
local notation "base" => finiteGlobalStructure hπ data 0 (Nat.zero_le n)
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m 0 (Nat.zero_le n)
local notation "s" => finiteGlobalArithmeticStructure hπ data 0 (Nat.zero_le n) m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q 0 (Nat.zero_le n)
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s

/-- Every ordered stage-zero chart pair has an actual full arithmetic output. -/
def arithmeticZeroStageActionQuotientOutput : pullback fa fb ⟶ pullback q t :=
  arithmeticAtlasOriginalActionQuotientOutput hπ data m 0 (Nat.zero_le n) a b

/-- Every output preserves its entire first original quotient structure map. -/
@[reassoc] theorem arithmeticZeroStageActionQuotientOutput_base :
    arithmeticZeroStageActionQuotientOutput hπ data m a b ≫ pullback.fst q t =
      pullback.fst fa fb ≫ fa :=
  arithmeticAtlasOriginalActionQuotientOutput_base hπ data m 0 (Nat.zero_le n) a b

/-- The second original arithmetic input has precisely the same coefficient map. -/
@[reassoc] theorem arithmeticZeroStageActionQuotientOutput_base_snd :
    arithmeticZeroStageActionQuotientOutput hπ data m a b ≫ pullback.fst q t =
      pullback.snd fa fb ≫ fb := by
  rw [arithmeticZeroStageActionQuotientOutput_base, pullback.condition]

/-- Integral projection recovers the original action on the two full smooth inputs. -/
@[reassoc] theorem arithmeticZeroStageActionQuotientOutput_integral :
    arithmeticZeroStageActionQuotientOutput hπ data m a b ≫ pullback.snd q t =
      arithmeticAtlasOriginalActionOutput hπ data m 0 (Nat.zero_le n) a b :=
  arithmeticAtlasOriginalActionQuotientOutput_integral hπ data m 0 (Nat.zero_le n) a b

end FLT.Mazur.WeierstrassDividedDepth
