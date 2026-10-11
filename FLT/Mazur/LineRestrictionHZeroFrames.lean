/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineRestrictionHZero

/-!
# Canonical scalar values of linear H0 restrictions

A section-preserving coefficient comparison transports a scalar endpoint formula
to the actual common target line. This connects field-linear H0 restriction with
the geometric endpoint transport without unfolding either comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.LinePullbackRestriction

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type u} [Field K] {X Y Z : Over (Spec (.of K))}
  (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (w : s ≫ p = q)
  {L : Z.left.Modules} {M : Y.left.Modules} (e : (pullback p.left).obj L ≅ M)
  (c : Γ(L, ⊤)) (d : Γ(M, ⊤)) (he : e.hom.app ⊤ (pullGlobal p.left L c) = d)

include he in
/-- A normalized endpoint formula gives the scalar value of actual linear H0 restriction. -/
theorem h0Along_value (x : ModuleScalarH Y.hom ((pullback p.left).obj L) 0)
    (r : Γ(X.left, ⊤))
    (hx : pullGlobal s.left M (e.hom.app ⊤ (moduleScalarH0Equiv Y.hom _ x)) =
      r • pullGlobal s.left M d) :
    moduleScalarH0Equiv X.hom _ (h0Along s p q w L x) = r • pullGlobal q.left L c := by
  rw [h0Along_sections, sealedAlong_eq_transport _ _ _ _ e]
  exact LineEndpointTransport.value p.left s.left q.left (congrArg Over.Hom.left w)
    e c d he _ r hx

include w he in
/-- Scalar cancellation in a compared endpoint frame holds in the original target line. -/
theorem h0Along_canonical_cancel
    (hd : Function.Injective (fun r : Γ(X.left, ⊤) ↦ r • pullGlobal s.left M d)) :
    Function.Injective (fun r : Γ(X.left, ⊤) ↦ r • pullGlobal q.left L c) :=
  LineEndpointTransport.canonical_cancel p.left s.left q.left
    (congrArg Over.Hom.left w) e c d he hd

end FLT.Mazur.LinePullbackRestriction
