/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaInput
public import FLT.Mazur.WeierstrassDividedReciprocalPrimeCoverage

/-!
# Reciprocal addition on full resolved atlas pairs

Common divided coordinates on any two retained charts give a new reciprocal
output domain in their full smooth relative product. Coincident residue
abscissae with nonzero ordinate difference are covered at every input depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalIntegralAtlasObject globalIntegralAtlasMap
  globalSmoothAtlasOpen globalSmoothAtlasMap
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b : Fin (j + 3)) (d : Data W π k)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ca" => globalSmoothAtlasMap hπ data j hj a
local notation "cb" => globalSmoothAtlasMap hπ data j hj b
local notation "ta" => ca ≫ t
local notation "tb" => cb ≫ t
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "P" => DividedPairRing W (π ^ k) d.b3 d.b4 d.b6
variable (f : globalIntegralAtlasObject data j hj a ⟶ chart d)
  (g : globalIntegralAtlasObject data j hj b ⟶ chart d)
variable
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj a ≫ finiteGlobalStructure hπ data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj b ≫ finiteGlobalStructure hπ data j hj)
local notation "left" => (globalSmoothAtlasOpen hπ data j hj a).ι ≫ f
local notation "right" => (globalSmoothAtlasOpen hπ data j hj b).ι ≫ g

local notation "input" => atlasPairFormulaInput hπ data j hj a b d f g hf hg
local notation "al" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "ar" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "O" => suppliedReciprocalDomain d al ar

/-- The reciprocal smooth-output open of the entire actual chart-pair product. -/
def atlasPairReciprocalOpen : (pullback ta tb).Opens := input ⁻¹ᵁ O

local notation "V" => atlasPairReciprocalOpen hπ data j hj a b d f g hf hg

/-- Construct the reciprocal output in the full resolved smooth locus. -/
def atlasPairReciprocalAddition : (V).toScheme ⟶ (U).toScheme :=
  (input ∣_ O) ≫ suppliedReciprocalResolvedAddition d al ar hπ data j hj

local notation "add" => atlasPairReciprocalAddition hπ data j hj a b d f g hf hg

/-- The reciprocal domain embeds into the exact full resolved product. -/
def atlasPairReciprocalInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b

instance atlasPairReciprocalInput_open :
    IsOpenImmersion (atlasPairReciprocalInput hπ data j hj a b d f g hf hg) := by
  unfold atlasPairReciprocalInput
  infer_instance

/-- The constructed reciprocal output retains the first input's coefficient point. -/
@[reassoc] theorem atlasPairReciprocalAddition_structure :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.fst t t ≫ t := by
  rw [atlasPairReciprocalAddition, Category.assoc,
    suppliedReciprocalResolvedAddition_structure, morphismRestrict_ι_assoc,
    atlasPairFormulaInput_structure]
  rfl

/-- The same output also retains the second actual input's coefficient point. -/
@[reassoc] theorem atlasPairReciprocalAddition_structure_snd :
    add ≫ t = (V).ι ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.snd t t ≫ t := by
  rw [atlasPairReciprocalAddition_structure, pullback.condition]

/-- The full reciprocal output contracts to the constructed original smooth formula. -/
@[reassoc] theorem atlasPairReciprocalAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ O) ≫ suppliedReciprocalOriginalSmooth d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
  rw [atlasPairReciprocalAddition, Category.assoc,
    suppliedReciprocalResolvedAddition_contraction]

/-- Equal residue abscissae with nonzero ordinate difference have actual resolved outputs. -/
theorem atlasPairReciprocalOpen_mem (p : (pullback ta tb : Scheme))
    (hx : al (x W (π ^ k) d.b3 d.b4 d.b6) - ar (x W (π ^ k) d.b3 d.b4 d.b6) ∈
      (input p).asIdeal)
    (hy : al (y W (π ^ k) d.b3 d.b4 d.b6) - ar (y W (π ^ k) d.b3 d.b4 d.b6) ∉
      (input p).asIdeal) : p ∈ V :=
  suppliedReciprocalDomain_mem d al ar (input p) hx hy

end FLT.Mazur.WeierstrassDividedDepth
