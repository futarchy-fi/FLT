/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTensorAtlas
public import FLT.Mazur.WeierstrassDividedInitialAtlasIndex
public import FLT.Mazur.WeierstrassDividedOlderAtlasIndex

/-!
# Original tensor algebras identify the complete indexed atlas

The terminal divided algebra, retained initial ModificationX algebra, and
each retained successive algebra give the actual indexed coefficient
pullbacks. The comparisons retain their maps into the finite model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "E₀" => initialExterior d₀
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
open scoped TensorProduct

/-- The actual terminal divided tensor algebra is indexed atlas object zero. -/
def finiteDividedTensorAtlasIso (j : ℕ) (hj : j ≤ n) :
    Spec (.of (WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 S)) ≅ finiteTensorAtlasObject hπ data S j hj 0 :=
  (finiteDividedTensorChart_isPullback hπ data S j hj).flip.isoPullback

/-- The terminal comparison retains the actual divided tensor atlas inclusion. -/
@[reassoc] theorem finiteDividedTensorAtlasIso_map (j : ℕ) (hj : j ≤ n) :
    (finiteDividedTensorAtlasIso hπ data S j hj).hom ≫ finiteTensorAtlasMap hπ data S j hj 0 =
      finiteDividedTensorChart hπ data S j hj :=
  (finiteDividedTensorChart_isPullback hπ data S j hj).flip.isoPullback_hom_snd

/-- The initial tensor chart is cartesian over its exact original finite atlas index. -/
theorem finiteInitialTensorChart_index_isPullback (j : ℕ) (hj : j ≤ n) :
    IsPullback (finiteInitialTensorChart hπ data S j hj)
      (TensorOpenChart.projection ≫ eqToHom (finiteInitialExteriorObject_eq data j hj).symm)
      (pullback.snd q (finiteStructure hπ data j hj))
      (finiteAtlasMap hπ data E₀ j hj ⟨j + 1, by omega⟩) := by
  apply (finiteInitialTensorChart_isPullback hπ data S j hj).of_iso
    (Iso.refl _) (Iso.refl _) (eqToIso (finiteInitialExteriorObject_eq data j hj).symm)
    (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, eqToIso.hom]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.comp_id, eqToIso.hom] using
      (finiteInitialChart_eq_index hπ data j hj).symm

/-- The actual initial tensor algebra is the final indexed atlas object, including k=0. -/
def finiteInitialTensorAtlasIso (j : ℕ) (hj : j ≤ n) :
    Spec (.of (S ⊗[R] WeierstrassModificationX.Coordinate W (π ^ start)
      (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀))) ≅
        finiteTensorAtlasObject hπ data S j hj ⟨j + 1, by omega⟩ :=
  (finiteInitialTensorChart_index_isPullback hπ data S j hj).flip.isoPullback

/-- The initial comparison retains the actual initial tensor inclusion. -/
@[reassoc] theorem finiteInitialTensorAtlasIso_map (j : ℕ) (hj : j ≤ n) :
    (finiteInitialTensorAtlasIso hπ data S j hj).hom ≫
      finiteTensorAtlasMap hπ data S j hj ⟨j + 1, by omega⟩ =
        finiteInitialTensorChart hπ data S j hj :=
  (finiteInitialTensorChart_index_isPullback hπ data S j hj).flip.isoPullback_hom_snd

variable (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

/-- Each older tensor chart is cartesian over its exact original finite atlas index. -/
theorem olderSuccessiveTensorChart_index_isPullback :
    IsPullback (olderSuccessiveTensorChart hπ data j hj r hr S)
      (TensorOpenChart.projection ≫ eqToHom (finiteOlderExteriorObject_eq data j hj r hr).symm)
      (pullback.snd q (finiteStructure hπ data (j + 1 + r) hr))
      (finiteAtlasMap hπ data E₀ (j + 1 + r) hr ⟨r + 1, by omega⟩) := by
  apply (olderSuccessiveTensorChart_isPullback hπ data j hj r hr S).of_iso
    (Iso.refl _) (Iso.refl _) (eqToIso (finiteOlderExteriorObject_eq data j hj r hr).symm)
    (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, eqToIso.hom]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.comp_id, eqToIso.hom] using
      (olderSuccessiveChart_eq_index hπ data j hj r hr).symm

/-- Every actual older successive tensor algebra is its corresponding indexed atlas object. -/
def olderSuccessiveTensorAtlasIso :
    Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) S)) ≅
        finiteTensorAtlasObject hπ data S (j + 1 + r) hr ⟨r + 1, by omega⟩ :=
  (olderSuccessiveTensorChart_index_isPullback hπ data S j hj r hr).flip.isoPullback

/-- The older comparison retains the actual original tensor chart inclusion. -/
@[reassoc] theorem olderSuccessiveTensorAtlasIso_map :
    (olderSuccessiveTensorAtlasIso hπ data S j hj r hr).hom ≫
      finiteTensorAtlasMap hπ data S (j + 1 + r) hr ⟨r + 1, by omega⟩ =
        olderSuccessiveTensorChart hπ data j hj r hr S :=
  (olderSuccessiveTensorChart_index_isPullback hπ data S j hj r hr).flip.isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
