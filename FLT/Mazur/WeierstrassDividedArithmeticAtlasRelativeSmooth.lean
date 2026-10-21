/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasTestPair
public import FLT.Mazur.WeierstrassDividedGlobalFiniteFlat
public import FLT.Mazur.SchemeSmoothLocusCartesian

/-!
# Full arithmetic smooth pairs from relative smooth input tests

The actual arithmetic smooth locus agrees with the atlas's full smooth domain.
Restricting a pair to those domains preserves its complete original coordinates.
This also applies to the exterior and terminal indices.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n)
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q k hk

local instance arithmeticAtlasRelativeSmooth_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every indexed arithmetic smooth domain is its complete relative smooth preimage. -/
theorem arithmeticAtlasSmoothOpen_relative (a : Fin (k + 3)) :
    O a = chart a ⁻¹ᵁ (s).smoothLocus := by
  unfold tensorIntegralAtlasSmoothOpen globalSmoothAtlasOpen
  rw [← Scheme.Hom.comp_preimage, arithmeticAtlasProjection_global,
    Scheme.Hom.comp_preimage]
  congr 1
  exact smoothLocus_preimage_of_isPullback (IsPullback.of_hasPullback base q)

/-- The test concerns the actual arithmetic input, at the original quotient order. -/
theorem arithmeticAtlasSmoothOpen_mem_relative (a : Fin (k + 3))
    (p : globalTensorAtlasObject hπ data Q k hk a) :
    p ∈ O a ↔ chart a p ∈ (s).smoothLocus := by
  rw [arithmeticAtlasSmoothOpen_relative]
  rfl

variable (a b : Fin (k + 3))
local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s
local notation "fa" => (O a).ι ≫ f
local notation "fb" => (O b).ι ≫ g
local notation "D" => arithmeticAtlasTestOpen hπ data m k hk a b
  (pullback.fst f g) (pullback.snd f g)
local notation "T" => arithmeticAtlasTestPair hπ data m k hk a b
  (pullback.fst f g) (pullback.snd f g) pullback.condition

/-- The first smooth restriction preserves the entire original indexed coordinate point. -/
@[reassoc] theorem arithmeticAtlasRelativePair_first :
    T ≫ pullback.fst fa fb ≫ (O a).ι = (D).ι ≫ pullback.fst f g := by
  rw [arithmeticAtlasTestPair, pullback.lift_fst_assoc, arithmeticAtlasTestLeft_inclusion]

/-- The second smooth restriction preserves its entire original indexed coordinate point. -/
@[reassoc] theorem arithmeticAtlasRelativePair_second :
    T ≫ pullback.snd fa fb ≫ (O b).ι = (D).ι ≫ pullback.snd f g := by
  rw [arithmeticAtlasTestPair, pullback.lift_snd_assoc, arithmeticAtlasTestRight_inclusion]

/-- Every relatively smooth full pair lifts to the actual smooth arithmetic atlas pair. -/
theorem arithmeticAtlasRelativePair_exists (p : (pullback f g : Scheme))
    (ha : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (hb : chart b (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ z : (pullback fa fb : Scheme),
      (O a).ι (pullback.fst fa fb z) = pullback.fst f g p ∧
      (O b).ι (pullback.snd fa fb z) = pullback.snd f g p := by
  let v : (D).toScheme := ⟨p,
    (arithmeticAtlasSmoothOpen_mem_relative hπ data m k hk a _).mpr ha,
    (arithmeticAtlasSmoothOpen_mem_relative hπ data m k hk b _).mpr hb⟩
  exact ⟨T v,
    congrArg (fun morphism => morphism v) (arithmeticAtlasRelativePair_first hπ data m k hk a b),
    congrArg (fun morphism => morphism v) (arithmeticAtlasRelativePair_second hπ data m k hk a b)⟩

end FLT.Mazur.WeierstrassDividedDepth
