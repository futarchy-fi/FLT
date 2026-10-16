/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPolygonMaps
public import FLT.Mazur.WeierstrassModificationXInitialPolygonBoundary

/-!
# Exact corrected initial-to-retained polygon endpoints

The actual original initial Laurent boundary is retained in full. Its
comparison to the retained arm includes the constructed parameter correction
and the cyclic edge inversion; neither change is silently discarded.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s : R)
  [Fact (IsNilpotent s)] (k : ℕ) (hk : 0 < k)

/-- The two oriented initial polygon labels meet the first retained labels in cyclic order. -/
@[reassoc] theorem initialPolygonLabel_retained_boundary (b : Bool) :
    leftBranchOpen R s ≫ (if b then (branchSwapIso R s).hom else 𝟙 _) ≫
      PolygonInfinitesimal.chart R s (2 * k + 3) (by omega) (initialPolygonIndex k b) =
    precedingBranch R s ≫ retainedPolygonMap R s k ⟨0, hk⟩ b := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Category.id_comp, retainedPolygonMap_false]
    rw [PolygonInfinitesimal.overlap, initialPolygonIndex_false_retained k hk]
  · simp only [↓reduceIte, retainedPolygonMap, ← Category.assoc,
      leftBranchOpen_branchSwapIso_preceding, precedingBranch_branchSwapIso]
    have hi : (edgeInversion R).inv = (edgeInversion R).hom := rfl
    rw [hi, Category.assoc, Category.assoc]
    congr 1
    rw [PolygonInfinitesimal.overlap, initialPolygonIndex_true_retained k hk]

variable (b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "B" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)))
local notation "T" => initialPolygonBoundaryParameter W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The entire original initial boundary reaches the retained arm with its exact correction. -/
@[reassoc] theorem initialPolygonMap_retained_boundary (b : Bool) :
    B ≫ initialPolygonMap W s k b =
      T ≫ precedingBranch R s ≫ retainedPolygonMap R s k ⟨0, hk⟩ b := by
  rw [initialPolygonMap, ← Category.assoc, initialPolygonChart_boundary, Category.assoc]
  rw [initialPolygonLabel_retained_boundary s k hk]

/-- On the original retained right boundary the required parameter change includes inversion. -/
@[reassoc] theorem initialPolygonMap_retained_right_boundary (b : Bool) :
    B ≫ initialPolygonMap W s k b =
      (T ≫ (edgeInversion R).hom) ≫ rightBranchOpen R s ≫
        retainedPolygonMap R s k ⟨0, hk⟩ b := by
  rw [initialPolygonMap_retained_boundary W s k hk]
  simp only [precedingBranch, Category.assoc]

/-- Removing the endpoint correction requires exactly equality with edge inversion. -/
theorem initialPolygonMap_original_endpoint_iff (b : Bool) :
    B ≫ initialPolygonMap W s k b =
      rightBranchOpen R s ≫ retainedPolygonMap R s k ⟨0, hk⟩ b ↔
        T = (edgeInversion R).inv := by
  rw [initialPolygonMap_retained_right_boundary W s k hk]
  have hmono : Mono (rightBranchOpen R s ≫ retainedPolygonMap R s k ⟨0, hk⟩ b) :=
    inferInstance
  constructor
  · intro h
    apply (Iso.comp_hom_eq_id (edgeInversion R)).mp
    apply (cancel_mono (rightBranchOpen R s ≫ retainedPolygonMap R s k ⟨0, hk⟩ b)).mp
    simpa only [Category.id_comp] using h
  · intro h
    rw [h, Iso.inv_hom_id, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
