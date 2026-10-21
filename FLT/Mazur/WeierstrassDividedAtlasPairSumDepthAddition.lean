/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairUnequalAddition
public import FLT.Mazur.WeierstrassDividedSumDepthCoverage

/-!
# Sum-depth outputs on the complete resolved atlas pairs

Retain each integral chart's own divided depth, map the exact full smooth
pair product into the unequal tensor product, and pull back the constructed
smooth output domain. No contracted-input smoothness is imposed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalIntegralAtlasObject globalIntegralAtlasMap
  globalSmoothAtlasOpen globalSmoothAtlasMap finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n k l : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b : Fin (j + 3)) (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (hdj : k + l ≤ j)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (h2 : W.a₂ = 0)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ta" => globalSmoothAtlasMap hπ data j hj a ≫ t
local notation "tb" => globalSmoothAtlasMap hπ data j hj b ≫ t
local notation "qa" => Spec.map (CommRingCat.ofHom
  (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6)))
local notation "qb" => Spec.map (CommRingCat.ofHom
  (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6)))
variable (f : globalIntegralAtlasObject data j hj a ⟶ chart d)
  (g : globalIntegralAtlasObject data j hj b ⟶ chart e)
variable
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj a ≫ finiteGlobalStructure hπ data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6))) =
      globalIntegralAtlasMap hπ data j hj b ≫ finiteGlobalStructure hπ data j hj)
local notation "left" => (globalSmoothAtlasOpen hπ data j hj a).ι ≫ f
local notation "right" => (globalSmoothAtlasOpen hπ data j hj b).ι ≫ g

local notation "input" => atlasPairUnequalFormulaInput hπ data j hj a b d e f g hf hg
local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e

local notation "O" => sumDepthDomain hπ d e hkl data (hdj.trans hj) dd ee h2 al ar

/-- The unequal-depth local-output domain inside the exact complete atlas pair. -/
def atlasPairSumDepthOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => atlasPairSumDepthOpen hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg

/-- Construct the output in the final resolved smooth locus. -/
def atlasPairSumDepthAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ sumDepthResolvedAddition hπ d e hkl data (hdj.trans hj) dd ee h2 al ar j hj hdj

/-- The local domain embeds in the complete resolved relative product. -/
def atlasPairSumDepthInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance atlasPairSumDepthInput_open :
    IsOpenImmersion (atlasPairSumDepthInput hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg) := by
  unfold atlasPairSumDepthInput
  infer_instance

/-- The constructed output has exactly the first input's coefficient point. -/
@[reassoc] theorem atlasPairSumDepthAddition_structure :
    atlasPairSumDepthAddition hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.fst t t ≫ t := by
  rw [atlasPairSumDepthAddition, Category.assoc, sumDepthResolvedAddition_structure,
    morphismRestrict_ι_assoc, atlasPairUnequalFormulaInput_structure]
  rfl

/-- The same output has exactly the second input's coefficient point. -/
@[reassoc] theorem atlasPairSumDepthAddition_structure_snd :
    atlasPairSumDepthAddition hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.snd t t ≫ t := by
  rw [atlasPairSumDepthAddition_structure, pullback.condition]

local notation "x₁" => al (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => al (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => ar (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => ar (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "α" => algebraMap R (UnequalPairRing d e) W.a₁

/-- Positive punctured branches in the complete pair lie in the actual sum-depth domain. -/
theorem atlasPairSumDepthOpen_positive_mem [IsLocalRing R] {m : ℕ}
    (D : SplitNodeDepth W π m) (hk : 0 < k) (hlt : k < l) (hm : 2 * (k + l) < m)
    (p : (pullback ta tb : Scheme))
    (hp : algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal)
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hy : y₁ ∈ (input p).asIdeal) (hv : y₂ ∈ (input p).asIdeal) : p ∈ V :=
  sumDepthDomain_positive_mem D d e hkl data (hdj.trans hj) dd ee h2 al ar
    hk hlt hm (input p) hp hx hu hy hv

end FLT.Mazur.WeierstrassDividedDepth
