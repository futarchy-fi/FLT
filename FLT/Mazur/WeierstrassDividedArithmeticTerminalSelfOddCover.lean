/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfShallow
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfTriple

/-!
# Actual terminal self-pair charts at odd final depth

At node depth 2*j+1 the feasible terminal stage is j. Stage one uses the
triple formula; larger stages use the shallow formula. Together with the
reciprocal formula these give complete outputs on a genuine two-open cover.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n nodeDepth : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => (1 : Fin (j + 3))
local notation "depth" => j
local notation "d" => data ⟨depth, Nat.lt_succ_of_le hj⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj idx
local notation "fa" => (O).ι ≫ chart idx ≫ s
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj idx idx
local notation "A" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

variable (hj0 : 0 < j) (hodd : nodeDepth = 2 * j + 1)
local notation "E" => arithmeticTerminalSelfReciprocalOpen hπ data m j hj

/-- Choose the actual endpoint or shallow formula at the feasible terminal stage. -/
def arithmeticTerminalSelfOddData :
    Σ V : (pullback fa fa).Opens, V.toScheme ⟶ pullback q t :=
  if h : j = 1 then
    ⟨arithmeticTerminalSelfTripleOpen node data m j hj (by omega),
      arithmeticTerminalSelfTripleQuotientOutput node data m j hj (by omega)⟩
  else
    ⟨arithmeticTerminalSelfShallowOpen node data m j hj (by omega) (by omega),
      arithmeticTerminalSelfShallowQuotientOutput node data m j hj (by omega) (by omega)⟩

/-- The selected genuine odd-depth formula domain. -/
def arithmeticTerminalSelfOddOpen : (pullback fa fa).Opens :=
  (arithmeticTerminalSelfOddData node data m j hj hj0 hodd).1

local notation "D" => arithmeticTerminalSelfOddOpen node data m j hj hj0 hodd

/-- The selected whole quotient output, with no reduction of coefficients. -/
def arithmeticTerminalSelfOddQuotientOutput : (D).toScheme ⟶ pullback q t :=
  (arithmeticTerminalSelfOddData node data m j hj hj0 hodd).2

/-- The odd-depth output preserves the complete first arithmetic coefficient map. -/
@[reassoc] theorem arithmeticTerminalSelfOddQuotientOutput_base :
    arithmeticTerminalSelfOddQuotientOutput node data m j hj hj0 hodd ≫ pullback.fst q t =
      (D).ι ≫ pullback.fst fa fa ≫ fa := by
  classical
  let property (v : Σ V : (pullback fa fa).Opens, V.toScheme ⟶ pullback q t) : Prop :=
    v.2 ≫ pullback.fst q t = v.1.ι ≫ pullback.fst fa fa ≫ fa
  change property (arithmeticTerminalSelfOddData node data m j hj hj0 hodd)
  unfold arithmeticTerminalSelfOddData
  split_ifs with h
  · exact arithmeticTerminalSelfTripleQuotientOutput_base node data m j hj (by omega)
  · exact arithmeticTerminalSelfShallowQuotientOutput_base node data m j hj (by omega) (by omega)

/-- The two actual formula domains cover the entire smooth terminal self-product. -/
theorem arithmeticTerminalSelfOdd_or_reciprocal_mem (p : (pullback fa fa : Scheme)) :
    p ∈ D ∨ p ∈ E := by
  classical
  unfold arithmeticTerminalSelfOddOpen arithmeticTerminalSelfOddData
  split_ifs with h
  · exact arithmeticTerminalSelfTriple_or_reciprocal_mem node data m j hj hj0 (by omega) p
  · exact arithmeticTerminalSelfShallow_or_reciprocal_mem node data m j hj (by omega) (by omega) p

/-- Index the two real odd-terminal formula domains. -/
def arithmeticTerminalSelfOddChart : Bool → (pullback fa fa).Opens
  | false => D
  | true => E

local notation "C" => arithmeticTerminalSelfOddChart node data m j hj hj0 hodd

/-- Both charts carry complete quotient-valued smooth outputs. -/
def arithmeticTerminalSelfOddChartOutput : (b : Bool) → (C b).toScheme ⟶ pullback q t
  | false => arithmeticTerminalSelfOddQuotientOutput node data m j hj hj0 hodd
  | true => arithmeticTerminalSelfReciprocalQuotientOutput node data m j hj

/-- All nilpotent arithmetic coefficients survive on both chart outputs. -/
@[reassoc] theorem arithmeticTerminalSelfOddChartOutput_base (b : Bool) :
    arithmeticTerminalSelfOddChartOutput node data m j hj hj0 hodd b ≫ pullback.fst q t =
      (C b).ι ≫ pullback.fst fa fa ≫ fa := by
  cases b
  · exact arithmeticTerminalSelfOddQuotientOutput_base node data m j hj hj0 hodd
  · exact arithmeticTerminalSelfReciprocalQuotientOutput_base node data m j hj

/-- The actual two odd-terminal domains exhaust the smooth terminal pair. -/
theorem arithmeticTerminalSelfOddChart_covers : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  rcases arithmeticTerminalSelfOdd_or_reciprocal_mem node data m j hj hj0 hodd p with hp | hp
  · exact (le_iSup (fun b => C b) false) hp
  · exact (le_iSup (fun b => C b) true) hp

/-- A genuine open cover of the complete smooth odd-terminal self-product. -/
def arithmeticTerminalSelfOddCover : (pullback fa fa : Scheme).OpenCover :=
  (pullback fa fa : Scheme).openCoverOfIsOpenCover C
    (arithmeticTerminalSelfOddChart_covers node data m j hj hj0 hodd)

end FLT.Mazur.WeierstrassDividedDepth
