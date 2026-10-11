/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart
public import FLT.Mazur.WeierstrassDividedGlobalInitialActionLaws

/-!
# The initial finite tensor chart retains the original global horizontal chart

The comparison keeps the actual coefficient pullback projection and the
initial finite-model isomorphism. No equality is inferred solely from the
contracted cubic on its exceptional fiber.
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
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => finiteGlobalInitialIso hπ data
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "g" => WeierstrassModificationX.xChart W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ≫
    WeierstrassGlobalModification.localChart W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (pow_ne_zero start hπ)

/-- The original integral initial chart retains its entire horizontal equation embedding. -/
@[reassoc] theorem finiteInitialChart_globalInitialIso :
    finiteInitialChart hπ data 0 (Nat.zero_le n) ≫
      finiteLocalChart hπ data 0 (Nat.zero_le n) ≫ (e).hom = g := by
  rw [finiteGlobalInitialIso_local]
  change (𝟙 _ ≫ (initialExterior d).exteriorChart) ≫
    (initialExteriorIso d).hom ≫ _ = _
  rw [Category.id_comp, initialExteriorIso_exterior_assoc]
  rfl

/-- The actual coefficient chart projects to the original initial global equation chart. -/
@[reassoc] theorem globalInitialTensorChart_initial_comparison :
    globalInitialTensorChart hπ data S 0 (Nat.zero_le n) ≫
      pullback.snd q (finiteGlobalStructure hπ data 0 (Nat.zero_le n)) ≫ (e).hom =
        TensorOpenChart.projection ≫ g := by
  rw [globalInitialTensorChart, Category.assoc, finiteLocalTensorEmbedding_square_assoc]
  rw [← Category.assoc]
  have h := (finiteInitialTensorChart_isPullback hπ data S 0 (Nat.zero_le n)).w
  rw [h, Category.assoc, finiteInitialChart_globalInitialIso]

/-- The inverse whole-model comparison also recovers the exact coefficient chart projection. -/
@[reassoc] theorem globalInitialTensorChart_initial_projection :
    TensorOpenChart.projection ≫ g ≫ (e).inv =
      globalInitialTensorChart hπ data S 0 (Nat.zero_le n) ≫
        pullback.snd q (finiteGlobalStructure hπ data 0 (Nat.zero_le n)) := by
  have h := congrArg (· ≫ (e).inv)
    (globalInitialTensorChart_initial_comparison hπ data S)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

end FLT.Mazur.WeierstrassDividedDepth
