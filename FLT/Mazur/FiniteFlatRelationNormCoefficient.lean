/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeRelationNorm
public import FLT.Mazur.FiniteFlatGlobalSections
public import FLT.Mazur.FiniteProjectiveAffineNorm
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Canonical full relation norm coefficients on affine charts

Finite flat presentation constructs the norm without a supplied basis. The
coefficient is invariant under the entire relation and its value commutes
with arbitrary Cartesian changes between affine charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatRelationNormCoefficient
open SchemeEffectiveEpiSections FiniteProjectiveAffineNorm
set_option backward.isDefEq.respectTransparency false
variable {D X : Scheme.{0}} (p q : D ⟶ X) [IsAffine D] [IsAffine X]
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The norm of the second-endpoint value, in the full invariant ring. -/
def coefficient (a : Γ(X, ⊤)) : compatibleFunctions p q :=
  ⟨norm p p.finite_appTop (FCurve.finiteFlat_appTop_projective p) (q.appTop a),
    AffineLocallyFreeRelationNorm.relationNorm_invariant p q
      (chart p p.finite_appTop (FCurve.finiteFlat_appTop_projective p))
      (chart_basis p p.finite_appTop (FCurve.finiteFlat_appTop_projective p))
      (chart_cover p p.finite_appTop (FCurve.finiteFlat_appTop_projective p)) e a⟩

/-- The norm detects the whole original fiber, including arrows leaving a smaller open. -/
theorem mem_basicOpen_coefficient (a : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen (coefficient p q e a).val ↔
      ∀ z : D, p z = x → q z ∈ X.basicOpen a := by
  rw [coefficient, mem_basicOpen_norm_iff, ← Scheme.preimage_basicOpen_top]
  rfl

variable {D' X' : Scheme.{0}} (p' q' : D' ⟶ X') [IsAffine D'] [IsAffine X']
  [IsFinite p'] [Flat p'] [LocallyOfFinitePresentation p']
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (f : X' ⟶ X) (g : D' ⟶ D) (H : IsPullback g p' p f)

include H in
/-- Full Cartesian changes preserve the constructed invariant norm value. -/
theorem coefficient_baseChange (hq' : g ≫ q = q' ≫ f) (a : Γ(X, ⊤)) :
    (coefficient p' q' e' (f.appTop a)).val = f.appTop (coefficient p q e a).val := by
  have he : q'.appTop (f.appTop a) = g.appTop (q.appTop a) :=
    congrArg (fun h ↦ h.appTop a) hq'.symm
  change norm p' p'.finite_appTop (FCurve.finiteFlat_appTop_projective p')
    (q'.appTop (f.appTop a)) = _
  rw [he]
  exact AffineNormCartesianGluing.norm_pullback_any H
    (chart p p.finite_appTop (FCurve.finiteFlat_appTop_projective p))
    (chart_basis p p.finite_appTop (FCurve.finiteFlat_appTop_projective p))
    (chart_cover p p.finite_appTop (FCurve.finiteFlat_appTop_projective p))
    (chart p' p'.finite_appTop (FCurve.finiteFlat_appTop_projective p'))
    (chart_basis p' p'.finite_appTop (FCurve.finiteFlat_appTop_projective p'))
    (chart_cover p' p'.finite_appTop (FCurve.finiteFlat_appTop_projective p')) (q.appTop a)

end FLT.Mazur.FiniteFlatRelationNormCoefficient
