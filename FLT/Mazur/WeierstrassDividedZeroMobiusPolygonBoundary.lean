/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroMobiusChart
public import FLT.Mazur.WeierstrassDividedInitialPolygonBoundary

/-!
# Both original initial-to-retained endpoints on the zero fiber

The complete initial opens embed at their original cyclic labels after
fractional tangent coordinates. With zero arithmetic ideal, both original
retained endpoint squares commute exactly, without a residual parameter change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (k : ℕ)
local instance zeroMobiusInitialParameter_nilpotent : Fact (IsNilpotent (0 : R)) := ⟨1, by simp⟩

/-- The complete fractional zero-fiber initial neighborhood at each original label. -/
def zeroInitialMobiusPolygonMap (b : Bool) : Spec (.of (PolynomialNodeOpen W 0)) ⟶
    PolygonInfinitesimal.scheme R 0 (2 * k + 3) (by omega) :=
  zeroInitialMobiusChart W ha ≫ (if b then (branchSwapIso R 0).hom else 𝟙 _) ≫
    PolygonInfinitesimal.chart R 0 (2 * k + 3) (by omega) (initialPolygonIndex k b)

instance zeroInitialMobiusPolygonMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (zeroInitialMobiusPolygonMap W ha k b) := by
  unfold zeroInitialMobiusPolygonMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- Both genuine full zero-fiber embeddings preserve the original coefficient structure. -/
@[reassoc] theorem zeroInitialMobiusPolygonMap_base (b : Bool) :
    zeroInitialMobiusPolygonMap W ha k b ≫
      PolygonInfinitesimal.toBase R 0 (2 * k + 3) (by omega) =
        Spec.map (CommRingCat.ofHom (algebraMap R (PolynomialNodeOpen W 0))) := by
  cases b <;> simp only [zeroInitialMobiusPolygonMap, Bool.false_eq_true, ↓reduceIte,
    Category.assoc, PolygonInfinitesimal.chart_toBase, retainedPolygonSwap_base, Category.id_comp]
  all_goals exact zeroInitialMobiusChart_structure W ha

variable (hk : 0 < k) (b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (hbot : I = ⊥)
local notation "B" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (laurentNodeRestriction W 0 b3 b4 b6 I hI ha (I.zero_mem) h2 h3 h4 h6)))

include hbot

/-- Both original full initial/retained endpoint squares commute on the zero arithmetic fiber. -/
@[reassoc] theorem zeroInitialMobiusPolygonMap_original_endpoint (b : Bool) :
    B ≫ zeroInitialMobiusPolygonMap W ha k b =
      rightBranchOpen R 0 ≫ retainedPolygonMap R 0 k ⟨0, hk⟩ b := by
  rw [zeroInitialMobiusPolygonMap, ← Category.assoc,
    zeroInitialMobiusChart_boundary W ha b3 b4 b6 I hI h2 h3 h4 h6 hbot,
    Category.assoc, initialPolygonLabel_retained_boundary 0 k hk]
  simp only [precedingBranch, ← Category.assoc]
  rw [show (edgeInversion R).hom ≫ (edgeInversion R).hom = 𝟙 _ from
    (edgeInversion R).hom_inv_id]
  exact congrArg (fun f : branchTorus R ⟶ chart R 0 ↦
    f ≫ retainedPolygonMap R 0 k ⟨0, hk⟩ b) (Category.id_comp (rightBranchOpen R 0))

end FLT.Mazur.WeierstrassDividedDepth
