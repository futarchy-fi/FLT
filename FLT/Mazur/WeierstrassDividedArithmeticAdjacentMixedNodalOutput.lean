/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedNodalHorizontalCover
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasTestTransition

/-!
# Normalized mixed outputs after the earlier retained input advances

Transfer the retained factor on its actual incidence domain, with the full
terminal factor unchanged. The target keeps its own depth and carries the
normalized quotient-valued formulas at the same final stage.
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
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  arithmeticFixedAdjacentPairOpen arithmeticFixedAdjacentPairTransfer
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k + 2 ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => (Fin.succ ⟨j - k, by omega⟩ : Fin (j + 3))
local notation "b" => (Fin.succ ⟨j - (k + 1), by omega⟩ : Fin (j + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O b).ι ≫ chart b ≫ s
local notation "fb" => (O 1).ι ≫ chart 1 ≫ s
local notation "f" => chart a ≫ s
local notation "f'" => chart b ≫ s
local notation "g" => chart 1 ≫ s
local notation "B" => arithmeticFixedAdjacentPairOpen hπ data m j hj k hk g
local notation "transfer" => arithmeticFixedAdjacentPairTransfer hπ data m j hj k hk g
local notation "x" => (B).ι ≫ pullback.fst f g
local notation "y" => (B).ι ≫ pullback.snd f g
local notation "z" => transfer ≫ pullback.fst f' g
local notation "w" => transfer ≫ pullback.snd f' g
omit [IsNoetherianRing R] in
/-- The adjacent transfer preserves the whole first arithmetic input. -/
@[reassoc] theorem arithmeticAdjacentMixedNodalInputs_first : x ≫ chart a = z ≫ chart b := by
  simpa only [Category.assoc] using
    (arithmeticFixedAdjacentPairTransfer_first hπ data m j hj k hk g).symm

omit [IsNoetherianRing R] in
/-- The adjacent transfer leaves the full terminal input unchanged. -/
@[reassoc] theorem arithmeticAdjacentMixedNodalInputs_second : y ≫ chart 1 = w ≫ chart 1 := by
  simpa only [Category.assoc] using congrArg (fun v => v ≫ chart 1)
    (arithmeticFixedAdjacentPairTransfer_second hπ data m j hj k hk g).symm

local notation "h₁" => arithmeticAdjacentMixedNodalInputs_first node data m j hj k hk
local notation "h₂" => arithmeticAdjacentMixedNodalInputs_second node data m j hj k hk

omit [IsNoetherianRing R] in
/-- The incidence source keeps its original common arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticAdjacentMixedNodalInputs_base :
    x ≫ chart a ≫ s = y ≫ chart 1 ≫ s := by
  simp only [Category.assoc]
  exact congrArg (fun v => (B).ι ≫ v)
    (show pullback.fst f g ≫ f = pullback.snd f g ≫ g from pullback.condition)

local notation "hb" => arithmeticAdjacentMixedNodalInputs_base node data m j hj k hk

/-- The exact full smooth part of the original adjacent boundary pair. -/
def arithmeticAdjacentMixedNodalSmoothOpen := arithmeticAtlasTestOpen hπ data m j hj a 1 x y

local notation "D" => arithmeticAdjacentMixedNodalSmoothOpen node data m j hj k hk

/-- The unchanged smooth incidence pair maps to the next retained/terminal pair. -/
def arithmeticAdjacentMixedNodalTarget : (D).toScheme ⟶ pullback fa fb :=
  arithmeticAtlasTestTarget hπ data m j hj a 1 b 1 x y z w h₁ h₂ hb

local notation "T" => arithmeticAdjacentMixedNodalTarget node data m j hj k hk

/-- The first actual resolved input is preserved, including its original coefficient map. -/
@[reassoc] theorem arithmeticAdjacentMixedNodalTarget_first :
    T ≫ pullback.fst fa fb ≫ (O b).ι ≫ chart b =
      (D).ι ≫ (B).ι ≫ pullback.fst f g ≫ chart a := by
  simpa only [arithmeticAdjacentMixedNodalTarget, arithmeticAdjacentMixedNodalSmoothOpen,
    Category.assoc] using
    (arithmeticAtlasTestTarget_first hπ data m j hj a 1 b 1 x y z w h₁ h₂ hb)

/-- The new tensor coordinate is exactly the existing explicit adjacent transfer. -/
@[reassoc] theorem arithmeticAdjacentMixedNodalTarget_coordinate :
    T ≫ pullback.fst fa fb ≫ (O b).ι = (D).ι ≫ z := by
  apply (cancel_mono (chart b)).mp
  simp only [Category.assoc]
  rw [arithmeticAdjacentMixedNodalTarget_first]
  simpa only [Category.assoc] using congrArg (fun v => (D).ι ≫ v) h₁

/-- The complete terminal input remains unchanged. -/
@[reassoc] theorem arithmeticAdjacentMixedNodalTarget_second :
    T ≫ pullback.snd fa fb ≫ (O 1).ι = (D).ι ≫ y := by
  apply (cancel_mono (chart 1)).mp
  simp only [Category.assoc]
  rw [arithmeticAdjacentMixedNodalTarget, arithmeticAtlasTestTarget_second]
  rfl

variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ (k + 1) + 2 * j)
local notation "E" => arithmeticMixedNodalReflectedChart
  node data m j hj (k + 1) (by omega) hdepth hnear

/-- Pull back the three actual normalized domains to the whole smooth incidence source. -/
def arithmeticAdjacentMixedNodalChart (c : Fin 3) : (D).toScheme.Opens := T ⁻¹ᵁ E c

local notation "C" => arithmeticAdjacentMixedNodalChart node data m j hj k hk hdepth hnear

/-- The actual adjacent incidence domain has full quotient-valued output formulas. -/
def arithmeticAdjacentMixedNodalOutput (c : Fin 3) : (C c).toScheme ⟶ pullback q t :=
  (T ∣_ E c) ≫ arithmeticMixedNodalReflectedQuotientOutput
    node data m j hj (k + 1) (by omega) hdepth hnear c

/-- The full original retained coefficient morphism survives the transfer and formula. -/
@[reassoc] theorem arithmeticAdjacentMixedNodalOutput_base (c : Fin 3) :
    arithmeticAdjacentMixedNodalOutput node data m j hj k hk hdepth hnear c ≫ pullback.fst q t =
      (C c).ι ≫ (D).ι ≫ (B).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticAdjacentMixedNodalOutput, Category.assoc,
    arithmeticMixedNodalReflectedQuotientOutput_base, morphismRestrict_ι_assoc]
  change (C c).ι ≫ T ≫ pullback.fst fa fb ≫ (O b).ι ≫ chart b ≫ s = _
  rw [arithmeticAdjacentMixedNodalTarget_first_assoc]

end FLT.Mazur.WeierstrassDividedDepth
