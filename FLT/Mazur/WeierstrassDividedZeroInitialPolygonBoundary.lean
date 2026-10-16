/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroInitialPolygon
public import FLT.Mazur.WeierstrassDividedInitialPolygonBoundary

/-!
# Both original initial-to-retained endpoints on the zero fiber

The complete initial opens embed at their original cyclic labels after
constant tangent-unit normalization. With zero arithmetic ideal, both original
retained endpoint squares commute exactly, without a residual parameter change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (u : Rˣ) (k : ℕ)
local instance zeroInitialParameter_nilpotent : Fact (IsNilpotent (0 : R)) := ⟨1, by simp⟩

/-- The complete normalized zero-fiber initial neighborhood at each original label. -/
def zeroInitialPolygonMap (b : Bool) : Spec (.of (PolynomialNodeOpen W 0)) ⟶
    PolygonInfinitesimal.scheme R 0 (2 * k + 3) (by omega) :=
  zeroInitialPolygonChart W u ≫ (if b then (branchSwapIso R 0).hom else 𝟙 _) ≫
    PolygonInfinitesimal.chart R 0 (2 * k + 3) (by omega) (initialPolygonIndex k b)

instance zeroInitialPolygonMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (zeroInitialPolygonMap W u k b) := by
  unfold zeroInitialPolygonMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- Both genuine full zero-fiber embeddings preserve the original coefficient structure. -/
@[reassoc] theorem zeroInitialPolygonMap_base (b : Bool) :
    zeroInitialPolygonMap W u k b ≫
      PolygonInfinitesimal.toBase R 0 (2 * k + 3) (by omega) =
        Spec.map (CommRingCat.ofHom (algebraMap R (PolynomialNodeOpen W 0))) := by
  cases b <;> simp only [zeroInitialPolygonMap, Bool.false_eq_true, ↓reduceIte, Category.assoc,
    PolygonInfinitesimal.chart_toBase, retainedPolygonSwap_base, Category.id_comp]
  all_goals exact zeroInitialPolygonChart_structure W u

variable (hk : 0 < k) (b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I)
  (ha : IsUnit W.a₁) (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (hbot : I = ⊥) (hu : (u : R) = W.a₁)
local notation "B" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (laurentNodeRestriction W 0 b3 b4 b6 I hI ha (I.zero_mem) h2 h3 h4 h6)))

include hbot hu

/-- Both original full initial/retained endpoint squares commute on the zero arithmetic fiber. -/
@[reassoc] theorem zeroInitialPolygonMap_original_endpoint (b : Bool) :
    B ≫ zeroInitialPolygonMap W u k b =
      rightBranchOpen R 0 ≫ retainedPolygonMap R 0 k ⟨0, hk⟩ b := by
  rw [zeroInitialPolygonMap, ← Category.assoc,
    zeroInitialPolygonChart_boundary W u b3 b4 b6 I hI ha h2 h3 h4 h6 hbot hu,
    Category.assoc, initialPolygonLabel_retained_boundary 0 k hk]
  simp only [precedingBranch, ← Category.assoc]
  rw [show (edgeInversion R).hom ≫ (edgeInversion R).hom = 𝟙 _ from
    (edgeInversion R).hom_inv_id]
  exact congrArg (fun f : branchTorus R ⟶ chart R 0 ↦
    f ≫ retainedPolygonMap R 0 k ⟨0, hk⟩ b) (Category.id_comp (rightBranchOpen R 0))

end FLT.Mazur.WeierstrassDividedDepth
