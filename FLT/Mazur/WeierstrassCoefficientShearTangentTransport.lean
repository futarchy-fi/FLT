/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTransport
public import FLT.Mazur.WeierstrassDividedTangentTransport

/-!
# The original tangent descent transport on the glued equations

Specialize the complete comparison to the actual integral tangent algebra.
It identifies whole-model transport and the genuine quadratic Cech comparison,
without imposing domain or Bezout hypotheses on the tangent algebra.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "root" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "q" => nodeTangentCover W
local notation "s" => coefficientShearGluedStructure hπ data S root j hj
variable {T : Scheme.{u}}
  (a b : T ⟶ Spec (.of (AdjoinRoot (nodeTangentPolynomial W))))
  (h : a ≫ nodeTangentCover W = b ≫ nodeTangentCover W)

/-- The complete sheared tangent-equation transport is the original finite-model transport. -/
@[reassoc] theorem coefficientShearTangentTransport_reconstruction :
    (coefficientShearTransport hπ data S root j hj a b h).hom ≫
        coefficientShearOverlapReconstruction hπ data S root j hj b =
      coefficientShearOverlapReconstruction hπ data S root j hj a ≫
        (finiteGlobalTangentTransport hπ data j hj a b h).hom :=
  coefficientShearTransport_reconstruction hπ data S root j hj a b h

/-- The whole-model comparison retains the actual triple-overlap tangent cocycle. -/
@[reassoc] theorem coefficientShearTangentTransport_comp (c : T ⟶ Spec (.of S))
    (hb : b ≫ q = c ≫ q) :
    (coefficientShearTransport hπ data S root j hj a b h).hom ≫
        (coefficientShearTransport hπ data S root j hj b c hb).hom =
      (coefficientShearTransport hπ data S root j hj a c (h.trans hb)).hom :=
  coefficientShearTransport_comp hπ data S root j hj a b h c hb

omit a b h in
/-- On the genuine quadratic overlap, reconstruction gives the original Cech isomorphism. -/
@[reassoc] theorem coefficientShearTangentCech_reconstruction :
    (coefficientShearTransport hπ data S root j hj
        (pullback.fst q q) (pullback.snd q q) pullback.condition).hom ≫
      coefficientShearOverlapReconstruction hπ data S root j hj (pullback.snd q q) =
    coefficientShearOverlapReconstruction hπ data S root j hj (pullback.fst q q) ≫
      (finiteGlobalTangentCechIso hπ data j hj).hom := by
  rw [finiteGlobalTangentCechIso_eq_transport]
  exact coefficientShearTangentTransport_reconstruction hπ data j hj _ _ pullback.condition

end FLT.Mazur.WeierstrassDividedDepth
