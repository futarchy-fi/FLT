/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart
public import FLT.Mazur.WeierstrassDividedGlobalStepOriginal
public import FLT.Mazur.WeierstrassDividedFiniteExteriorPullback

/-!
# Every global successor retains the full initial chart

The actual initial equation chart forms an identity pullback under each
global step. This also identifies its tensor projection and gives uniqueness
over that chart for arbitrary schemes of points.
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
local notation "E" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

/-- The original integral equation chart inside the entire finite global model. -/
def globalInitialChart (j : ℕ) (hj : j ≤ n) :=
  finiteInitialChart hπ data j hj ≫ finiteLocalChart hπ data j hj

instance globalInitialChart_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (globalInitialChart hπ data j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The retained chart has the same integral coefficient morphism at every stage. -/
@[reassoc] theorem globalInitialChart_structure (j : ℕ) (hj : j ≤ n) :
    globalInitialChart hπ data j hj ≫ finiteGlobalStructure hπ data j hj =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (WeierstrassModificationX.Coordinate W (π ^ start)
          (data ⟨0, Nat.zero_lt_succ n⟩).b3 (data ⟨0, Nat.zero_lt_succ n⟩).b4
          (data ⟨0, Nat.zero_lt_succ n⟩).b6))) := by
  rw [globalInitialChart, Category.assoc, finiteLocalChart_structure,
    finiteInitialChart_structure]

/-- The original initial equation chart is the full inverse image at every global step. -/
theorem globalInitialChart_step_isPullback (j : ℕ) (hj : j + 1 ≤ n) :
    IsPullback (𝟙 (E).carrier) (globalInitialChart hπ data (j + 1) hj)
      (globalInitialChart hπ data j (Nat.le_of_succ_le hj))
      (finiteGlobalStep hπ data j hj) := by
  have H := (IsPullback.of_id_fst
    (f := finiteRetained hπ data E j (Nat.le_of_succ_le hj))).paste_vert
      ((finiteExterior hπ data E j (Nat.le_of_succ_le hj)).step_exterior_isPullback
        hπ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
  have H' := H.paste_vert (finiteGlobalStep_local_isPullback hπ data j hj)
  simpa only [globalInitialChart, finiteInitialChart, finiteRetained, finiteExterior,
    finiteStep, Category.assoc] using H'

/-- The retained integral initial chart commutes with the actual global successor. -/
@[reassoc] theorem globalInitialChart_step (j : ℕ) (hj : j + 1 ≤ n) :
    globalInitialChart hπ data (j + 1) hj ≫ finiteGlobalStep hπ data j hj =
      globalInitialChart hπ data j (Nat.le_of_succ_le hj) := by
  simpa only [Category.id_comp] using (globalInitialChart_step_isPullback hπ data j hj).w.symm

/-- Every coefficient tensor chart projects to exactly this original integral chart. -/
@[reassoc] theorem globalInitialTensorChart_integralProjection
    (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n) :
    globalInitialTensorChart hπ data S j hj ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (finiteGlobalStructure hπ data j hj) =
      TensorOpenChart.projection ≫ globalInitialChart hπ data j hj := by
  rw [globalInitialTensorChart, Category.assoc, finiteLocalTensorEmbedding_square]
  rw [← Category.assoc, (finiteInitialTensorChart_isPullback hπ data S j hj).w]
  rfl

/-- An arbitrary point over the unchanged initial chart has its unique displayed lift. -/
theorem globalInitialChart_step_lift_unique (j : ℕ) (hj : j + 1 ≤ n)
    {T : Scheme.{u}} (x : T ⟶ (E).carrier)
    (f : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hf : f ≫ finiteGlobalStep hπ data j hj =
      x ≫ globalInitialChart hπ data j (Nat.le_of_succ_le hj)) :
    f = x ≫ globalInitialChart hπ data (j + 1) hj := by
  have H := globalInitialChart_step_isPullback hπ data j hj
  have hx := H.lift_fst x f hf.symm
  simp only [Category.comp_id] at hx
  have hy := H.lift_snd x f hf.symm
  rw [hx] at hy
  exact hy.symm

end FLT.Mazur.WeierstrassDividedDepth
