/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasRelativeSmooth

/-!
# Whole arithmetic pairs and their actual smooth restriction

The smooth atlas pair embeds openly into the full indexed pair. Restricting
and then including recovers the original pair morphism, not only its points.
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

/-- Include the entire smooth arithmetic pair in its original full indexed product. -/
def arithmeticSmoothPairInclusion : pullback fa fb ⟶ pullback f g :=
  pullback.map _ _ _ _ (O a).ι (O b).ι (𝟙 _)
    (by rw [Category.comp_id]) (by rw [Category.comp_id])

local notation "inc" => arithmeticSmoothPairInclusion hπ data m k hk a b

/-- The full smooth pair is an actual open subchart of the original pair. -/
instance arithmeticSmoothPairInclusion_open : IsOpenImmersion inc := by
  unfold arithmeticSmoothPairInclusion
  infer_instance

/-- The first original arithmetic coordinate is unchanged by inclusion. -/
@[reassoc] theorem arithmeticSmoothPairInclusion_first :
    inc ≫ pullback.fst f g = pullback.fst fa fb ≫ (O a).ι := pullback.lift_fst _ _ _

/-- The second original arithmetic coordinate is unchanged by inclusion. -/
@[reassoc] theorem arithmeticSmoothPairInclusion_second :
    inc ≫ pullback.snd f g = pullback.snd fa fb ≫ (O b).ι := pullback.lift_snd _ _ _

local notation "D" => arithmeticAtlasTestOpen hπ data m k hk a b
  (pullback.fst f g) (pullback.snd f g)
local notation "T" => arithmeticAtlasTestPair hπ data m k hk a b
  (pullback.fst f g) (pullback.snd f g) pullback.condition

/-- Smooth restriction followed by inclusion recovers the complete original pair morphism. -/
@[reassoc] theorem arithmeticAtlasTestPair_inclusion : T ≫ inc = (D).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, arithmeticSmoothPairInclusion_first]
    exact arithmeticAtlasRelativePair_first hπ data m k hk a b
  · rw [Category.assoc, arithmeticSmoothPairInclusion_second]
    exact arithmeticAtlasRelativePair_second hπ data m k hk a b

local instance arithmeticSmoothPairInclusion_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every smooth full pair lifts with equality in the whole original relative product. -/
theorem arithmeticSmoothPairInclusion_exists (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ z : (pullback fa fb : Scheme), inc z = p := by
  let v : (D).toScheme := ⟨p,
    (arithmeticAtlasSmoothOpen_mem_relative hπ data m k hk a _).mpr hs,
    (arithmeticAtlasSmoothOpen_mem_relative hπ data m k hk b _).mpr ht⟩
  exact ⟨T v, congrArg (fun morphism => morphism v)
    (arithmeticAtlasTestPair_inclusion hπ data m k hk a b)⟩

end FLT.Mazur.WeierstrassDividedDepth
