/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairUnequalAddition
public import FLT.Mazur.WeierstrassDividedNodalWiderReflectedNegative

/-!
# Negative wider reflected-depth outputs on the complete resolved atlas pairs

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
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n k l m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b : Fin (j + 3)) (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (hdj : m - k - l ≤ j)
  (hm : k + 2 * l ≤ m) (htop : m ≤ 2 * (k + l))
local notation "hπ" => D.uniformizer_ne_zero
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
      globalIntegralAtlasMap D.uniformizer_ne_zero data j hj a ≫
        finiteGlobalStructure D.uniformizer_ne_zero data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6))) =
      globalIntegralAtlasMap D.uniformizer_ne_zero data j hj b ≫
        finiteGlobalStructure D.uniformizer_ne_zero data j hj)
local notation "left" => (globalSmoothAtlasOpen hπ data j hj a).ι ≫ f
local notation "right" => (globalSmoothAtlasOpen hπ data j hj b).ι ≫ g

local notation "input" => atlasPairUnequalFormulaInput hπ data j hj a b d e f g hf hg
local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e

local notation "O" => nodalWiderReflectedNegativeDomain D d e hkl data (hdj.trans hj) hm htop al ar

/-- The unequal-depth local-output domain inside the exact complete atlas pair. -/
def nodalWiderReflectedAtlasPairNegativeOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => nodalWiderReflectedAtlasPairNegativeOpen D data j hj a b d e hkl
  hdj hm htop f g hf hg

/-- Construct the output in the final resolved smooth locus. -/
def nodalWiderReflectedAtlasPairNegativeAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫
    nodalWiderReflectedNegativeAddition D d e hkl data (hdj.trans hj) hm htop al ar j hj hdj

/-- The local domain embeds in the complete resolved relative product. -/
def nodalWiderReflectedAtlasPairNegativeInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance nodalWiderReflectedAtlasPairNegativeInput_open :
    IsOpenImmersion
      (nodalWiderReflectedAtlasPairNegativeInput D data j hj a b d e hkl
        hdj hm htop f g hf hg) := by
  unfold nodalWiderReflectedAtlasPairNegativeInput
  infer_instance

/-- The constructed output has exactly the first input's coefficient point. -/
@[reassoc] theorem nodalWiderReflectedAtlasPairNegativeAddition_structure :
    nodalWiderReflectedAtlasPairNegativeAddition D data j hj a b d e hkl hdj hm htop f g hf hg ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.fst t t ≫ t := by
  rw [nodalWiderReflectedAtlasPairNegativeAddition, Category.assoc,
    nodalWiderReflectedNegativeAddition_structure,
    morphismRestrict_ι_assoc, atlasPairUnequalFormulaInput_structure]
  rfl

/-- The same output has exactly the second input's coefficient point. -/
@[reassoc] theorem nodalWiderReflectedAtlasPairNegativeAddition_structure_snd :
    nodalWiderReflectedAtlasPairNegativeAddition D data j hj a b d e hkl hdj hm htop f g hf hg ≫ t =
      (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.snd t t ≫ t := by
  rw [nodalWiderReflectedAtlasPairNegativeAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
