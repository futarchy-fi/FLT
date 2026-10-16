/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioPuncture
public import FLT.Mazur.WeierstrassDividedFactorRatioRetainedBoundary

/-!
# The complete corrected retained comparison at both cyclic labels

The full retained node map reaches the same polygon as the initial chart.
Their entire original Laurent boundaries agree at the first retained depth.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
  (d : R) (hd : s = π * d)
local notation "τ" => initialTangentSmoothing W ha s
variable [Fact (IsNilpotent (initialTangentSmoothing W ha s))] (k : ℕ)
local notation "F" => retainedFactorRatioChart W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd
local notation "b3" => π * c3
local notation "b4" => π * c4
local notation "b6" => π ^ 2 * c6
local notation "H3" => I.mul_mem_left π h3
local notation "H4" => I.mul_mem_left π h4
local notation "H6" => I.mul_mem_left (π ^ 2) h6
local notation "E" => factorRatioLaurentIso W ha s b3 b4 b6 I hI hs h2 H3 H4 H6

/-- The full corrected original node maps to each prescribed retained polygon label. -/
def retainedFactorRatioPolygonMap (a : Fin k) (b : Bool) :
    PolygonSmoothing.chart R π ⟶ PolygonInfinitesimal.scheme R τ (2 * k + 3) (by omega) :=
  F ≫ retainedPolygonMap R τ k a b
local notation "P" => retainedFactorRatioPolygonMap W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd k

/-- Both retained labels preserve the entire reciprocal Laurent boundary. -/
@[reassoc] theorem retainedFactorRatioPolygonMap_right (a : Fin k) (b : Bool) :
    rightBranchOpen R π ≫ P a b =
      (E).hom ≫ precedingBranch R τ ≫ retainedPolygonMap R τ k a b := by
  rw [retainedFactorRatioPolygonMap, ← Category.assoc,
    retainedFactorRatioChart_right_boundary]
  simp only [precedingBranch, Category.assoc]

local notation "r" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 H3 H4 H6
local notation "hr" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 H3 H4 H6
local notation "hm" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 H3 H4 H6
local notation "G" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 H3 H4 H6)))

/-- The original initial and first retained full boundaries agree at both actual cyclic labels. -/
@[reassoc] theorem retainedFactorRatioPolygonMap_initial_boundary (hk : 0 < k) (b : Bool) :
    G ≫ factorRatioInitialPolygonMap W ha s τ (initialTangentSmoothing_factor W ha s)
      k b3 b4 b6 r hr I hI hm H3 b = rightBranchOpen R π ≫ P ⟨0, hk⟩ b := by
  rw [factorRatioInitialPolygonMap_retained_boundary W ha s τ
    (initialTangentSmoothing_factor W ha s) k hk, retainedFactorRatioPolygonMap_right]

end FLT.Mazur.WeierstrassDividedDepth
