/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSplitCocone
public import FLT.Mazur.WeierstrassDividedZeroSplitCycleCoverage

/-!
# Surjectivity of the actual cyclic normalization cocone leg

The complete projective component coproduct reaches every point of the original
fiber. This does not assert finiteness, a scheme pushout or a polygon isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)

/-- The actual complete component coproduct reaches every original global fiber point. -/
theorem zeroSplitCycleNormalization_surjective :
    Function.Surjective (zeroSplitCycleNormalization hπ data D s hs hstart hk hp).left := by
  intro z
  obtain ⟨i, x, hx⟩ := zeroSplitCycleComponent_cover hπ data D s hs hstart hk hp z
  refine ⟨(PolygonPinching.componentι K (2 * s + 3) i).left x, ?_⟩
  have H := congrArg (fun f => f.left x)
    (zeroSplitCycleNormalization_ι hπ data D s hs hstart hk hp i)
  exact H.trans hx

/-- The normalization leg has no missing component or point in its global image. -/
theorem zeroSplitCycleNormalization_range :
    Set.range (zeroSplitCycleNormalization hπ data D s hs hstart hk hp).left = Set.univ :=
  (zeroSplitCycleNormalization_surjective hπ data D s hs hstart hk hp).range_eq

end FLT.Mazur.WeierstrassDividedDepth
