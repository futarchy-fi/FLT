/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedMixedKernelAction

/-!
# Scheme-valued action on the entire divided kernel closure

The mixed action evaluates on arbitrary test schemes. Its inclusion, naturality,
structure map and restriction to the original smooth kernel are retained.
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

/-- Evaluate the original smooth kernel action at arbitrary full-closure points. -/
def finiteGlobalMixedKernelPointAction {T : Scheme}
    (a : T ⟶ genericClosureSmoothPart W i)
    (b : T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i) (h : a ≫ s = b ≫ f) :
    T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i :=
  pullback.lift a b h ≫ finiteGlobalMixedKernelAction hπ data j hj hΔ G g

/-- Evaluation retains the entire ambient action, including all exceptional inputs. -/
@[reassoc] theorem finiteGlobalMixedKernelPointAction_inclusion {T : Scheme}
    (a : T ⟶ genericClosureSmoothPart W i)
    (b : T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i) (h : a ≫ s = b ≫ f) :
    finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g a b h ≫ c =
      finiteGlobalPointAction hπ data j hj (a ≫ v) (b ≫ c)
        (by simpa only [Category.assoc, genericClosureSmoothInclusion_structure,
          finiteGlobalKernelClosureStructure] using h) := by
  rw [finiteGlobalMixedKernelPointAction, Category.assoc,
    finiteGlobalMixedKernelAction_inclusion, finiteGlobalMixedKernelAmbientAction,
    ← finiteGlobalPointAction_comp]
  simp only [pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- The full-closure output has the same original coefficient map. -/
@[reassoc] theorem finiteGlobalMixedKernelPointAction_structure {T : Scheme}
    (a : T ⟶ genericClosureSmoothPart W i)
    (b : T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i) (h : a ≫ s = b ≫ f) :
    finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g a b h ≫ f = a ≫ s := by
  rw [finiteGlobalMixedKernelPointAction, Category.assoc,
    finiteGlobalMixedKernelAction_structure, pullback.lift_fst_assoc]

/-- Evaluation is natural even for nonflat test-scheme morphisms. -/
theorem finiteGlobalMixedKernelPointAction_comp {T V : Scheme} (p : V ⟶ T)
    (a : T ⟶ genericClosureSmoothPart W i)
    (b : T ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i) (h : a ≫ s = b ≫ f) :
    finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g (p ≫ a) (p ≫ b)
        (by simpa only [Category.assoc] using congrArg (p ≫ ·) h) =
      p ≫ finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g a b h := by
  unfold finiteGlobalMixedKernelPointAction
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd,
    Category.assoc]

/-- The action on two original smooth kernel points is their original multiplication. -/
theorem finiteGlobalMixedKernelPointAction_smooth {T : Scheme}
    (a b : T ⟶ genericClosureSmoothPart W i) (h : a ≫ s = b ≫ s) :
    finiteGlobalMixedKernelPointAction hπ data j hj hΔ G g a (b ≫ e)
        (by rw [Category.assoc, finiteGlobalKernelSmoothEmbedding_structure]; exact h) =
      pullback.lift a b h ≫ m ≫ e := by
  have he : pullback.lift a (b ≫ e)
      (by rw [Category.assoc, finiteGlobalKernelSmoothEmbedding_structure]; exact h) =
      pullback.lift a b h ≫ finiteGlobalMixedKernelPair hπ data j hj hΔ i := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, finiteGlobalMixedKernelPair_fst,
        pullback.lift_fst]
    · simp only [pullback.lift_snd, Category.assoc, finiteGlobalMixedKernelPair_snd,
        pullback.lift_snd_assoc]
  rw [finiteGlobalMixedKernelPointAction, he, Category.assoc,
    finiteGlobalMixedKernelAction_smooth]

end FLT.Mazur.WeierstrassDividedDepth
