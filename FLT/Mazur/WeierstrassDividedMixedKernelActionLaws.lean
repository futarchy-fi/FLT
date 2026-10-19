/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedMixedKernelPoints
public import FLT.Mazur.WeierstrassClosureSmoothGroupOperations
public import FLT.Mazur.WeierstrassDividedGlobalActionAssociativity

/-!
# Laws for the original smooth kernel acting on the full divided closure

Cancel the actual closed inclusion to inherit zero, inverse cancellation and
associativity on every full-closure test point, including exceptional components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
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

local notation "z" => (genericClosureSmoothOverZero W hΔ G g).left
local notation "neg" => (genericClosureSmoothOverNegation W hΔ G g).left

/-- The actual original smooth-kernel zero fixes every point of the full closure. -/
theorem finiteGlobalMixedKernelPointAction_zero {T : Scheme}
    (b : T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i) :
    finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g (b ≫ f ≫ z) b
        (by rw [Category.assoc, Category.assoc,
          (show z ≫ s = 𝟙 (Spec (.of R)) from
            (genericClosureSmoothOverZero W hΔ G g).w), Category.comp_id]) = b := by
  apply (cancel_mono c).mp
  rw [finiteGlobalMixedKernelPointAction_inclusion]
  have hz : z ≫ v = integralSmoothZero W :=
    congrArg Over.Hom.left (genericClosureSmoothOverZero_inclusion W hΔ G g)
  simp only [Category.assoc, hz]
  exact finiteGlobalPointAction_zero hπ data j hj (b ≫ c)

/-- The actual negative original kernel parameter undoes its full-closure action. -/
theorem finiteGlobalMixedKernelPointAction_neg_cancel {T : Scheme}
    (a : T ⟶ genericClosureSmoothPart W i)
    (b : T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i) (h : a ≫ s = b ≫ f) :
    finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g (a ≫ neg)
      (finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g a b h)
      (by rw [Category.assoc, (show neg ≫ s = s from (genericClosureSmoothOverNegation W hΔ G g).w),
        finiteGlobalMixedKernelPointAction_structure]) = b := by
  apply (cancel_mono c).mp
  simp only [finiteGlobalMixedKernelPointAction_inclusion]
  have hn : neg ≫ v = v ≫ integralSmoothNegation W :=
    congrArg Over.Hom.left (genericClosureSmoothOverNegation_inclusion W hΔ G g)
  simpa only [Category.assoc, hn] using
    finiteGlobalPointAction_neg_cancel hπ data j hj (a ≫ v) (b ≫ c)
      (by simpa only [Category.assoc, genericClosureSmoothInclusion_structure,
        finiteGlobalKernelClosureStructure] using h)

/-- An original kernel parameter also undoes the action of its actual negative. -/
theorem finiteGlobalMixedKernelPointAction_cancel_neg {T : Scheme}
    (a : T ⟶ genericClosureSmoothPart W i)
    (b : T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i) (h : a ≫ s = b ≫ f) :
    finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g a
      (finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g (a ≫ neg) b
        (by rw [Category.assoc,
          (show neg ≫ s = s from (genericClosureSmoothOverNegation W hΔ G g).w)]; exact h))
      (by rw [finiteGlobalMixedKernelPointAction_structure, Category.assoc,
        (show neg ≫ s = s from (genericClosureSmoothOverNegation W hΔ G g).w)]) = b := by
  apply (cancel_mono c).mp
  simp only [finiteGlobalMixedKernelPointAction_inclusion]
  have hn : neg ≫ v = v ≫ integralSmoothNegation W :=
    congrArg Over.Hom.left (genericClosureSmoothOverNegation_inclusion W hΔ G g)
  simpa only [Category.assoc, hn] using
    finiteGlobalPointAction_cancel_neg hπ data j hj (a ≫ v) (b ≫ c)
      (by simpa only [Category.assoc, genericClosureSmoothInclusion_structure,
        finiteGlobalKernelClosureStructure] using h)

/-- The original kernel multiplication acts associatively on the full divided closure. -/
theorem finiteGlobalMixedKernelPointAction_assoc {T : Scheme}
    (a b : T ⟶ genericClosureSmoothPart W i)
    (x : T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i)
    (hab : a ≫ s = b ≫ s) (hbx : b ≫ s = x ≫ f) :
    finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g (pullback.lift a b hab ≫ m) x
        (by rw [Category.assoc, genericClosureSmoothMultiplication_structure,
          pullback.lift_fst_assoc]; exact hab.trans hbx) =
      finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g a
        (finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g b x hbx)
        (by rw [finiteGlobalMixedKernelPointAction_structure]; exact hab) := by
  apply (cancel_mono c).mp
  simp only [finiteGlobalMixedKernelPointAction_inclusion]
  have hm : (pullback.lift a b hab ≫ m) ≫ v =
      smoothPairPointAddition W (a ≫ v) (b ≫ v)
        (by simpa only [Category.assoc, genericClosureSmoothInclusion_structure] using hab) := by
    rw [Category.assoc, genericClosureSmoothMultiplication_inclusion]
    unfold smoothPairPointAddition
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;>
      simp only [Category.assoc, genericClosureSmoothAmbientPair_fst,
        genericClosureSmoothAmbientPair_snd, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  simpa only [hm] using
    finiteGlobalPointAction_assoc hπ data j hj (a ≫ v) (b ≫ v) (x ≫ c)
      (by simpa only [Category.assoc, genericClosureSmoothInclusion_structure] using hab)
      (by simpa only [Category.assoc, genericClosureSmoothInclusion_structure,
        finiteGlobalKernelClosureStructure] using hbx)

end FLT.Mazur.WeierstrassDividedDepth
