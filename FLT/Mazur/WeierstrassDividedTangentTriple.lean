/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentCechCocycle
public import FLT.Mazur.WeierstrassDividedTangentTransport

/-!
# The finite-model cocycle on the genuine tangent triple overlap

The three coefficient lifts live on the actual iterated fiber product.
Their finite-model transports satisfy the cocycle, and restriction to any
double overlap recovers the original finite-model Cech isomorphism.
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
  (j : ℕ) (hj : j ≤ n)
local notation "q" => nodeTangentCover W
local notation "p₁" => pullback.fst q q
local notation "p₂" => pullback.snd q q
local notation "t₁" => pullback.fst p₂ p₁
local notation "t₂" => pullback.snd p₂ p₁
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "ys" => pullback.fst q base
local notation "yx" => pullback.snd q base

omit [IsDomain R] [IsBezout R] in
/-- Compatibility of the first two genuine triple-overlap coefficient lifts. -/
theorem finiteGlobalTangentTriple_first_middle : (t₁ ≫ p₁) ≫ q = (t₁ ≫ p₂) ≫ q := by
  rw [Category.assoc, Category.assoc, pullback.condition (f := q) (g := q)]

omit [IsDomain R] [IsBezout R] in
/-- Compatibility of the middle and last lifts, using the original triple fiber product. -/
theorem finiteGlobalTangentTriple_middle_last : (t₁ ≫ p₂) ≫ q = (t₂ ≫ p₂) ≫ q := by
  rw [pullback.condition (f := p₂) (g := p₁), Category.assoc, Category.assoc,
    pullback.condition (f := q) (g := q)]

local notation "h₁₂" => finiteGlobalTangentTriple_first_middle (W := W)
local notation "h₂₃" => finiteGlobalTangentTriple_middle_last (W := W)

/-- The model's actual triple-overlap cocycle, with the original integral model retained. -/
@[reassoc] theorem finiteGlobalTangentTriple_cocycle :
    (finiteGlobalTangentTransport hπ data j hj (t₁ ≫ p₁) (t₁ ≫ p₂) h₁₂).hom ≫
        (finiteGlobalTangentTransport hπ data j hj (t₁ ≫ p₂) (t₂ ≫ p₂) h₂₃).hom =
      (finiteGlobalTangentTransport hπ data j hj (t₁ ≫ p₁) (t₂ ≫ p₂)
        ((h₁₂).trans h₂₃)).hom :=
  finiteGlobalTangentTransport_comp hπ data j hj _ _ h₁₂ _ h₂₃

/-- Pulling the overlap comparison along any map gives precisely the same model transport. -/
@[reassoc] theorem finiteGlobalTangentCechIso_restrict {T : Scheme.{u}}
    (k : T ⟶ pullback q q) :
    (finiteGlobalTangentTransport hπ data j hj (k ≫ p₁) (k ≫ p₂)
        (by rw [Category.assoc, Category.assoc, pullback.condition])).hom ≫
        CartesianCoefficientTransport.restrict p₂ k =
      CartesianCoefficientTransport.restrict p₁ k ≫
        (finiteGlobalTangentCechIso hπ data j hj).hom := by
  rw [finiteGlobalTangentCechIso_eq_transport]
  exact CartesianCoefficientTransport.map_restrict
    (IsPullback.of_hasPullback q base).flip p₁ p₂ pullback.condition k

omit [IsDomain R] [IsBezout R] in
/-- The direct first-to-last coefficient pair is exactly the actual Cech composition map. -/
theorem finiteGlobalTangentTriple_outer_pair :
    nodeTangentCechCompose W ≫ p₁ = t₁ ≫ p₁ ∧
      nodeTangentCechCompose W ≫ p₂ = t₂ ≫ p₂ :=
  ⟨nodeTangentCechCompose_fst W, nodeTangentCechCompose_snd W⟩

end FLT.Mazur.WeierstrassDividedDepth
