/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairIso

/-!
# Transporting actual local outputs to the smooth arithmetic product

Open source images in the full product restrict to opens in the product of
smooth charts. The lift preserves both inputs and every supplied output.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (a b : Fin (k + 3))
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q k hk
local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s
local notation "fa" => (O a).ι ≫ f
local notation "fb" => (O b).ι ≫ g
local notation "inc" => arithmeticSmoothPairInclusion hπ data m k hk a b
variable {ι : Type} (X : ι → Scheme)
  (source : (i : ι) → X i ⟶ pullback
    (arithmeticTensorAtlasMap hπ data m k hk a ≫
      finiteGlobalArithmeticStructure hπ data k hk m)
    (arithmeticTensorAtlasMap hπ data m k hk b ≫
      finiteGlobalArithmeticStructure hπ data k hk m))
  [∀ i, IsOpenImmersion (source i)]

/-- Each complete local source image restricts to the product of smooth charts. -/
def arithmeticSmoothPairSourceChart (i : ι) : (pullback fa fb).Opens :=
  inc ⁻¹ᵁ (source i).opensRange

local notation "C" => arithmeticSmoothPairSourceChart hπ data m k hk a b X source

/-- Recover the original local source, including its full scheme structure. -/
def arithmeticSmoothPairSourceLift (i : ι) : (C i).toScheme ⟶ X i :=
  (inc ∣_ (source i).opensRange) ≫ (source i).isoOpensRange.inv

local notation "lift" => arithmeticSmoothPairSourceLift hπ data m k hk a b X source

/-- Both entire original inputs survive the source lift. -/
@[reassoc] theorem arithmeticSmoothPairSourceLift_inclusion (i : ι) :
    lift i ≫ source i = (C i).ι ≫ inc := by
  rw [arithmeticSmoothPairSourceLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

local instance arithmeticSmoothPairSourceCover_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Smooth full-product source coverage gives actual coverage of the smooth product. -/
theorem arithmeticSmoothPairSourceChart_covers
    (covers : ∀ p : (pullback f g : Scheme),
      chart a (pullback.fst f g p) ∈ (s).smoothLocus →
      chart b (pullback.snd f g p) ∈ (s).smoothLocus →
      ∃ i, ∃ z : X i, source i z = p) : (⨆ i, C i) = ⊤ := by
  apply top_unique
  intro p _
  have hp := arithmeticSmoothPairInclusion_mem hπ data m k hk a b p
  obtain ⟨i, z, hz⟩ := covers (inc p)
    ((arithmeticAtlasSmoothOpen_mem_relative hπ data m k hk a _).mp hp.1)
    ((arithmeticAtlasSmoothOpen_mem_relative hπ data m k hk b _).mp hp.2)
  exact (le_iSup (fun i => C i) i) (show p ∈ C i from ⟨z, hz⟩)

local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Actual local formulas induce a full open cover with quotient outputs on the smooth pair. -/
theorem arithmeticSmoothPairSource_outputCover
    (covers : ∀ p : (pullback f g : Scheme),
      chart a (pullback.fst f g p) ∈ (s).smoothLocus →
      chart b (pullback.snd f g p) ∈ (s).smoothLocus →
      ∃ i, ∃ z : X i, source i z = p)
    (output : (i : ι) → X i ⟶ pullback q t)
    (output_base : ∀ i, output i ≫ pullback.fst q t = source i ≫ pullback.fst f g ≫ f) :
    ∃ (cover : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (i : cover.I₀) → cover.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = cover.f i ≫ pullback.fst fa fb ≫ fa := by
  let cover := (pullback fa fb : Scheme).openCoverOfIsOpenCover C
    (arithmeticSmoothPairSourceChart_covers hπ data m k hk a b X source covers)
  refine ⟨cover, fun i => lift i ≫ output i, ?_⟩
  intro i
  change (lift i ≫ output i) ≫ pullback.fst q t = (C i).ι ≫ pullback.fst fa fb ≫ fa
  rw [Category.assoc, output_base, arithmeticSmoothPairSourceLift_inclusion_assoc,
    arithmeticSmoothPairInclusion_first_assoc]

end FLT.Mazur.WeierstrassDividedDepth
