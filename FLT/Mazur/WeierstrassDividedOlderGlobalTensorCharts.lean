/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
public import FLT.Mazur.WeierstrassDividedTensorAtlasComparison

/-!
# Older original tensor algebras in the global indexed atlas

Every retained successive tensor algebra embeds at its precise global index.
The comparison uses the existing finite tensor atlas isomorphism and preserves
all original functions through the cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The original older tensor algebra as an open of every later global coefficient model. -/
def olderGlobalTensorChart :=
  olderSuccessiveTensorChart hπ data j hj r hr S ≫
    finiteLocalTensorEmbedding hπ data S (j + 1 + r) hr

instance olderGlobalTensorChart_isOpenImmersion :
    IsOpenImmersion (olderGlobalTensorChart hπ data S j hj r hr) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The actual older chart is precisely global atlas index r+2, with its canonical source iso. -/
@[reassoc] theorem olderGlobalTensorChart_eq_index :
    (olderSuccessiveTensorAtlasIso hπ data S j hj r hr).hom ≫
      globalTensorAtlasMap hπ data S (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
        olderGlobalTensorChart hπ data S j hj r hr := by
  change _ ≫ (finiteTensorAtlasMap hπ data S (j + 1 + r) hr ⟨r + 1, by omega⟩ ≫ _) = _
  rw [olderSuccessiveTensorAtlasIso_map_assoc]
  rfl

/-- Every original older tensor function retains its full cubic contraction globally. -/
@[reassoc] theorem olderGlobalTensorChart_toCurve :
    olderGlobalTensorChart hπ data S j hj r hr ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      TensorOpenChart.projection ≫ xContraction hπ d e ≫ toCurve d := by
  rw [olderGlobalTensorChart, Category.assoc, finiteLocalTensorEmbedding_toCurve,
    olderSuccessiveTensorChart_toCurve]

/-- The full older global chart retains its original extended coefficient structure. -/
@[reassoc] theorem olderGlobalTensorChart_structure :
    olderGlobalTensorChart hπ data S j hj r hr ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S
        (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
          (Data.b3 e) (Data.b4 e) (Data.b6 e) S))) := by
  rw [olderGlobalTensorChart, Category.assoc, finiteLocalTensorEmbedding_structure,
    olderSuccessiveTensorChart_structure]

end FLT.Mazur.WeierstrassDividedDepth
