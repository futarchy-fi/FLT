/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
public import FLT.Mazur.WeierstrassDividedTensorAtlasComparison

/-!
# The original initial tensor chart at its global atlas index

The full ModificationX tensor algebra is retained at the last global index,
with its original cubic contraction and coefficient structure, including start zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The entire initial tensor algebra embeds in the projective coefficient pullback. -/
def globalInitialTensorChart :=
  finiteInitialTensorChart hπ data S j hj ≫ finiteLocalTensorEmbedding hπ data S j hj

instance globalInitialTensorChart_isOpenImmersion :
    IsOpenImmersion (globalInitialTensorChart hπ data S j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The original initial algebra is exactly the last global indexed object. -/
theorem globalInitialTensorChart_eq_index :
    (finiteInitialTensorAtlasIso hπ data S j hj).hom ≫
      globalTensorAtlasMap hπ data S j hj (Fin.succ ⟨j + 1, by omega⟩) =
        globalInitialTensorChart hπ data S j hj := by
  change _ ≫ (finiteTensorAtlasMap hπ data S j hj _ ≫ _) = _
  rw [finiteInitialTensorAtlasIso_map_assoc]
  rfl

/-- The entire initial tensor chart retains every original cubic function. -/
@[reassoc] theorem globalInitialTensorChart_toCurve :
    globalInitialTensorChart hπ data S j hj ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      TensorOpenChart.projection ≫
        WeierstrassModificationX.toCurve W (π ^ start)
          (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
          (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) := by
  rw [globalInitialTensorChart, Category.assoc, finiteLocalTensorEmbedding_toCurve,
    finiteInitialTensorChart_toCurve]

/-- The whole initial chart retains the extended coefficient structure. -/
@[reassoc] theorem globalInitialTensorChart_structure :
    globalInitialTensorChart hπ data S j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S
        (S ⊗[R] WeierstrassModificationX.Coordinate W (π ^ start)
          (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)))) := by
  rw [globalInitialTensorChart, Category.assoc, finiteLocalTensorEmbedding_structure,
    finiteInitialTensorChart_structure]

end FLT.Mazur.WeierstrassDividedDepth
