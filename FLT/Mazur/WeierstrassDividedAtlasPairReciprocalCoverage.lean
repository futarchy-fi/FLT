/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairReciprocalAddition
public import FLT.Mazur.WeierstrassDividedAtlasPairIntermediateAddition
public import FLT.Mazur.WeierstrassDividedNodalIntermediateReciprocalCoverage

/-!
# Intermediate and reciprocal coverage on the actual resolved atlas product

There is no slope-denominator condition in this coverage result. The only
remaining restrictions are the nodal depth range and vertical nonvanishing
of the common contracted inputs. All domains remain opens of the full pair.
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
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure rootShearCurve
  nodalSecondShear nodalSecondQuotient
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : k + r ≤ n)
  (j : ℕ) (hj : j ≤ n) (hrj : k + r ≤ j)
  (a b : Fin (j + 3)) (d : Data W π k)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ca" => globalSmoothAtlasMap hπ data j hj a
local notation "cb" => globalSmoothAtlasMap hπ data j hj b
local notation "ta" => ca ≫ t
local notation "tb" => cb ≫ t
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R A))
variable (f : globalIntegralAtlasObject data j hj a ⟶ chart d)
  (g : globalIntegralAtlasObject data j hj b ⟶ chart d)
variable
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap D.uniformizer_ne_zero data j hj a ≫
        finiteGlobalStructure D.uniformizer_ne_zero data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap D.uniformizer_ne_zero data j hj b ≫
        finiteGlobalStructure D.uniformizer_ne_zero data j hj)
local notation "input" => atlasPairFormulaInput hπ data j hj a b d f g hf hg
local notation "al" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "ar" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hr d al ar

local notation "V" => atlasPairIntermediateOpen D hdepth hrk hrm data hr j hj a b d f g hf hg
local notation "P" => DividedPairRing W (π ^ k) d.b3 d.b4 d.b6
local notation "dx" => al (x W (π ^ k) d.b3 d.b4 d.b6) -
  ar (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "E" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 al ar
local notation "δ" => verticalDerivative W (π ^ k) d.b3 d.b4 d.b6

local notation "Q" => atlasPairReciprocalOpen hπ data j hj a b d f g hf hg

/-- Both actual output domains cover every vertically smooth common-coordinate nodal pair. -/
theorem atlasPairIntermediate_or_reciprocal_mem (p : (pullback ta tb : Scheme))
    (hk : 0 < k) (hm : m < 4 * k) (hrmax : r = m - 3 * k)
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (ha : al δ ∉ (input p).asIdeal) (hb : ar δ ∉ (input p).asIdeal) :
    p ∈ V ∨ p ∈ Q :=
  nodalIntermediate_or_reciprocal_cover D hdepth hrk hrm data hr d al ar
    hk hm hrmax (input p) hp ha hb

/-- A missed actual pair must have a vertically singular contracted input. -/
theorem atlasPairIntermediate_reciprocal_missing_input (p : (pullback ta tb : Scheme))
    (hk : 0 < k) (hm : m < 4 * k) (hrmax : r = m - 3 * k)
    (hp : algebraMap R P π ∈ (input p).asIdeal)
    (hv : p ∉ V) (hq : p ∉ Q) :
    al δ ∈ (input p).asIdeal ∨ ar δ ∈ (input p).asIdeal :=
  nodalIntermediate_reciprocal_missing_input D hdepth hrk hrm data hr d al ar
    hk hm hrmax (input p) hp hv hq

end FLT.Mazur.WeierstrassDividedDepth
