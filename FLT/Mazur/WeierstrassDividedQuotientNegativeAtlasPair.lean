/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairUnequalAddition
public import FLT.Mazur.WeierstrassDividedQuotientNegativeContraction

/-!
# Negative quotient outputs on the complete resolved atlas pairs

Retain each integral chart's own divided depth, map the exact full smooth
pair product into the unequal tensor product, and pull back the constructed
negative-branch output domain. The full input pair is retained.
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
  (dd : BranchQuotientData d) (ee : BranchQuotientData e) (h2 : W.a₂ = 0)
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

local notation "O" => quotientNegativeSumDepthDomain hπ d e hkl data (hdj.trans hj) dd ee h2 al ar

/-- The unequal-depth local-output domain inside the exact complete atlas pair. -/
def quotientAtlasPairNegativeSumDepthOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => quotientAtlasPairNegativeSumDepthOpen hπ data j hj a b d e hkl
  hdj dd ee h2 f g hf hg

/-- Construct the output in the final resolved smooth locus. -/
def quotientAtlasPairNegativeSumDepthAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫
    quotientNegativeSumDepthAddition hπ d e hkl data (hdj.trans hj) dd ee h2 al ar j hj hdj

/-- The local domain embeds in the complete resolved relative product. -/
def quotientAtlasPairNegativeSumDepthInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance quotientAtlasPairNegativeSumDepthInput_open :
    IsOpenImmersion
      (quotientAtlasPairNegativeSumDepthInput hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg) := by
  unfold quotientAtlasPairNegativeSumDepthInput
  infer_instance

/-- The constructed output has exactly the first input's coefficient point. -/
@[reassoc] theorem quotientAtlasPairNegativeSumDepthAddition_structure :
    quotientAtlasPairNegativeSumDepthAddition hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.fst t t ≫ t := by
  rw [quotientAtlasPairNegativeSumDepthAddition, Category.assoc,
    quotientNegativeSumDepthAddition_structure,
    morphismRestrict_ι_assoc, atlasPairUnequalFormulaInput_structure]
  rfl

/-- The same output has exactly the second input's coefficient point. -/
@[reassoc] theorem quotientAtlasPairNegativeSumDepthAddition_structure_snd :
    quotientAtlasPairNegativeSumDepthAddition hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.snd t t ≫ t := by
  rw [quotientAtlasPairNegativeSumDepthAddition_structure, pullback.condition]

local notation "T" => UnequalDepthSecantRing hπ d e hkl al ar
local notation "old" => dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 al
  (unequalDepthRight hπ d e hkl ar) d.factor3 d.factor4 d.factor6

/-- The complete pair domain maps to the original secant localization. -/
def quotientAtlasPairNegativeSumDepthSecantInput : (V).toScheme ⟶ Spec (.of T) :=
  (input ∣_ O) ≫
    quotientNegativeSumDepthSecantInput hπ d e hkl al ar data (hdj.trans hj) dd ee h2

/-- The secant comparison uses the original pair input morphism. -/
@[reassoc] theorem quotientAtlasPairNegativeSumDepthSecantInput_structure :
    quotientAtlasPairNegativeSumDepthSecantInput hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg ≫
        Spec.map (CommRingCat.ofHom (algebraMap (UnequalPairRing d e) T)) =
      (V).ι ≫ input := by
  rw [quotientAtlasPairNegativeSumDepthSecantInput, Category.assoc,
    quotientNegativeSumDepthSecantInput_structure, morphismRestrict_ι]
  rfl

/-- The resolved negative-branch law contracts to the unchanged original secant. -/
@[reassoc] theorem quotientAtlasPairNegativeSumDepthAddition_original :
    quotientAtlasPairNegativeSumDepthAddition hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      quotientAtlasPairNegativeSumDepthSecantInput hπ data j hj a b d e hkl hdj dd ee h2 f g hf hg ≫
        old := by
  simp only [quotientAtlasPairNegativeSumDepthAddition,
    quotientAtlasPairNegativeSumDepthSecantInput,
    Category.assoc, quotientNegativeSumDepthAddition_original]

end FLT.Mazur.WeierstrassDividedDepth
