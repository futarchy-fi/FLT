/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedOlderCoordinates
public import FLT.Mazur.WeierstrassDividedAtlasPairUnequalAddition

/-!
# Unequal-depth addition on retained older charts

Use the preceding creation depth of each retained chart separately. The
source remains their full smooth relative product; only the constructed
output domain is restricted. Opposite punctured branches belong to it.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedOlderLowerCoordinates retainedOlderFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l < j) (hkl : k ≤ l)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, by omega⟩
local notation "e" => data ⟨l, by omega⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => retainedOlderLowerCoordinates hπ data j hj l hl l le_rfl
local notation "hf" => retainedOlderLowerCoordinates_structure hπ data j hj k hk k le_rfl
local notation "hg" => retainedOlderLowerCoordinates_structure hπ data j hj l hl l le_rfl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj a ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj b ≫ t

/-- Both retained charts supply their own preceding-depth coordinates on the full pair. -/
def olderUnequalFormulaInput : pullback ta tb ⟶ Spec (.of (UnequalPairRing d e)) :=
  atlasPairUnequalFormulaInput hπ data j hj a b d e f g hf hg

local notation "input" => olderUnequalFormulaInput hπ data j hj k l hk hl

/-- The first factor is exactly the first retained chart's own coordinates. -/
@[reassoc] theorem olderUnequalFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) =
      pullback.fst ta tb ≫ (globalSmoothAtlasOpen hπ data j hj a).ι ≫ f :=
  atlasPairUnequalFormulaInput_left hπ data j hj a b d e f g hf hg

/-- The deeper factor has not been contracted to the shallower depth. -/
@[reassoc] theorem olderUnequalFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom) =
      pullback.snd ta tb ≫ (globalSmoothAtlasOpen hπ data j hj b).ι ≫ g :=
  atlasPairUnequalFormulaInput_right hπ data j hj a b d e f g hf hg

/-- The actual unequal-depth output domain on this entire retained pair. -/
def olderUnequalOpen : (pullback ta tb).Opens :=
  atlasPairUnequalOpen hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + l) - (0 + k) ≤ j; omega) f g hf hg

local notation "V" => olderUnequalOpen hπ data j hj k l hk hl hkl

/-- The constructed output lands in the final resolved smooth locus. -/
def olderUnequalAddition : (V).toScheme ⟶ (U).toScheme :=
  atlasPairUnequalAddition hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + l) - (0 + k) ≤ j; omega) f g hf hg

/-- The domain includes into the complete resolved relative product. -/
def olderUnequalInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance olderUnequalInput_open :
    IsOpenImmersion (olderUnequalInput hπ data j hj k l hk hl hkl) := by
  unfold olderUnequalInput
  infer_instance

/-- Addition preserves the first input's actual coefficient point. -/
@[reassoc] theorem olderUnequalAddition_structure :
    olderUnequalAddition hπ data j hj k l hk hl hkl ≫ t =
      olderUnequalInput hπ data j hj k l hk hl hkl ≫ pullback.fst t t ≫ t := by
  unfold olderUnequalAddition olderUnequalInput
  rw [Category.assoc]
  exact atlasPairUnequalAddition_structure hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + l) - (0 + k) ≤ j; omega) f g hf hg

/-- Addition also preserves the second input's coefficient point. -/
@[reassoc] theorem olderUnequalAddition_structure_snd :
    olderUnequalAddition hπ data j hj k l hk hl hkl ≫ t =
      olderUnequalInput hπ data j hj k l hk hl hkl ≫ pullback.snd t t ≫ t := by
  rw [olderUnequalAddition_structure, pullback.condition]

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "α" => algebraMap R (UnequalPairRing d e) W.a₁

/-- Opposite branches at the two own depths have a constructed resolved sum. -/
theorem olderUnequalOpen_opposite_mem [IsLocalRing R] {m : ℕ}
    (D : SplitNodeDepth W π m) (hk0 : 0 < k) (hlt : k < l) (hm : 2 * l < m)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hb : (y₁ ∈ (input p).asIdeal ∧ y₂ + α * x₂ ∈ (input p).asIdeal) ∨
      (y₁ + α * x₁ ∈ (input p).asIdeal ∧ y₂ ∈ (input p).asIdeal)) : p ∈ V :=
  atlasPairUnequalOpen_opposite_mem hπ data j hj a b d e (Nat.add_le_add_left hkl 0)
    (by change (0 + l) - (0 + k) ≤ j; omega)
    f g hf hg D (by change 0 < 0 + k; omega) (by change 0 + k < 0 + l; omega)
    (by change 2 * (0 + l) < m; omega) p hp hx hu hb

end FLT.Mazur.WeierstrassDividedDepth
