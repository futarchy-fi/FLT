/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedMixedKernelPair
public import FLT.Mazur.WeierstrassGenericClosureSmoothMultiplication
public import FLT.Mazur.WeierstrassDividedGlobalOriginalSmoothPoints

/-!
# The original smooth kernel preserves the entire resolved kernel closure

Its already proved multiplication detects the closed equations on a dense
mixed product. This constructs an action on the full divided closure, retaining
all special-fiber points and the exact ambient action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  (G : CommGrp (Over (Spec (.of K)))) (g : G ⟶ integralCurveGroup _ hΔ)
  [IsClosedImmersion g.hom.hom.hom.left]
  [Flat (g.hom.hom.hom.left ≫ integralCurveStructure (W.map (algebraMap R K)))]
local notation "i" => g.hom.hom.hom.left
local notation "s" => genericClosureSmoothStructure W i
local notation "f" => finiteGlobalKernelClosureStructure hπ data j hj hΔ i
local notation "e" => finiteGlobalKernelSmoothEmbedding hπ data j hj hΔ i
local notation "c" => finiteGlobalKernelClosureInclusion hπ data j hj hΔ i
local notation "v" => genericClosureSmoothInclusion W i
local notation "m" => genericClosureSmoothMultiplication W hΔ G g

/-- Act on the full divided closure with an original smooth kernel parameter. -/
def finiteGlobalMixedKernelAmbientAction : pullback s f ⟶ finiteGlobalModel hπ data j hj :=
  finiteGlobalPointAction hπ data j hj (pullback.fst s f ≫ v) (pullback.snd s f ≫ c) (by
    simp only [Category.assoc, genericClosureSmoothInclusion_structure]
    exact pullback.condition)

omit [IsNoetherianRing R] in
/-- On dense smooth pairs the ambient action is the existing original kernel multiplication. -/
theorem finiteGlobalMixedKernelPair_action :
    finiteGlobalMixedKernelPair hπ data j hj hΔ i ≫
        finiteGlobalMixedKernelAmbientAction hπ data j hj hΔ G g = (m ≫ e) ≫ c := by
  rw [finiteGlobalMixedKernelAmbientAction, ← finiteGlobalPointAction_comp]
  simp only [Category.assoc, finiteGlobalMixedKernelPair_fst_assoc,
    finiteGlobalMixedKernelPair_snd_assoc, finiteGlobalKernelSmoothEmbedding_inclusion,
    genericClosureSmoothMultiplication_inclusion_assoc]
  have he := finiteGlobalPointAction_smoothEmbedding hπ data j hj
    (pullback.fst s s ≫ v) (pullback.snd s s ≫ v)
    (by
      simp only [Category.assoc, genericClosureSmoothInclusion_structure]
      exact pullback.condition)
  simpa only [Category.assoc, smoothPairPointAddition, genericClosureSmoothAmbientPair] using he

/-- Closed equations extend the original smooth kernel action to the entire divided closure. -/
@[irreducible] def finiteGlobalMixedKernelAction :
    pullback s f ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i := by
  let _ := finiteGlobalMixedKernelPair_dense hπ data j hj hΔ i
  exact DenseClosedRestriction.lift (finiteGlobalMixedKernelPair hπ data j hj hΔ i) c
    (finiteGlobalMixedKernelAmbientAction hπ data j hj hΔ G g) (m ≫ e)
    (finiteGlobalMixedKernelPair_action hπ data j hj hΔ G g)

/-- The whole kernel action is exactly the restriction of the constructed ambient action. -/
@[reassoc] theorem finiteGlobalMixedKernelAction_inclusion :
    finiteGlobalMixedKernelAction hπ data j hj hΔ G g ≫ c =
      finiteGlobalMixedKernelAmbientAction hπ data j hj hΔ G g := by
  unfold finiteGlobalMixedKernelAction
  let _ := finiteGlobalMixedKernelPair_dense hπ data j hj hΔ i
  exact DenseClosedRestriction.lift_inclusion (finiteGlobalMixedKernelPair hπ data j hj hΔ i) c
    (finiteGlobalMixedKernelAmbientAction hπ data j hj hΔ G g) (m ≫ e)
    (finiteGlobalMixedKernelPair_action hπ data j hj hΔ G g)

/-- Restriction back to the original smooth kernel recovers its actual multiplication. -/
@[reassoc] theorem finiteGlobalMixedKernelAction_smooth :
    finiteGlobalMixedKernelPair hπ data j hj hΔ i ≫
      finiteGlobalMixedKernelAction hπ data j hj hΔ G g = m ≫ e := by
  apply (cancel_mono c).mp
  rw [Category.assoc, finiteGlobalMixedKernelAction_inclusion, finiteGlobalMixedKernelPair_action]

/-- The full preserved kernel keeps its original integral coefficient morphism. -/
@[reassoc] theorem finiteGlobalMixedKernelAction_structure :
    finiteGlobalMixedKernelAction hπ data j hj hΔ G g ≫ f = pullback.fst s f ≫ s := by
  calc
    _ = (finiteGlobalMixedKernelAction hπ data j hj hΔ G g ≫ c) ≫
        finiteGlobalStructure hπ data j hj := (Category.assoc _ _ _).symm
    _ = finiteGlobalMixedKernelAmbientAction hπ data j hj hΔ G g ≫
        finiteGlobalStructure hπ data j hj :=
      congrArg (· ≫ finiteGlobalStructure hπ data j hj)
        (finiteGlobalMixedKernelAction_inclusion hπ data j hj hΔ G g)
    _ = (pullback.fst s f ≫ v) ≫ integralSmoothStructure W :=
      finiteGlobalPointAction_structure hπ data j hj _ _ _
    _ = _ := by rw [Category.assoc, genericClosureSmoothInclusion_structure]

end FLT.Mazur.WeierstrassDividedDepth
