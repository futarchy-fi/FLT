/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGroupRelativeDimension

/-!
# Dimension of every smooth open in the original whole family

The classified geometric fibers determine relative dimension one on any
smooth open of the original curve. This applies to the preimage of a model
smooth locus without asserting flatness of that model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The actual smooth open has relative dimension one, over an arbitrary base scheme. -/
theorem smoothOpen_relativeDimension {S : Scheme} (E : GeneralizedEllipticCurve S) :
    SmoothOfRelativeDimension 1 (E.curve.hom.smoothLocus.ι ≫ E.curve.hom) := by
  let _ : IsIso E.smoothIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map E.smoothIso.inv))
  change SmoothOfRelativeDimension 1 (curveSmoothOpen E.curve).hom
  rw [← E.smoothIso.inv.w]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1)
    (inferInstanceAs (SmoothOfRelativeDimension 1 E.group.hom)) _

/-- Any relatively smooth open in the whole original family is a relative curve. -/
theorem smooth_open_relativeDimension {S : Scheme} (E : GeneralizedEllipticCurve S)
    (U : E.curve.left.Opens) [Smooth (U.ι ≫ E.curve.hom)] :
    SmoothOfRelativeDimension 1 (U.ι ≫ E.curve.hom) := by
  have hU : U ≤ E.curve.hom.smoothLocus := by
    intro x hx
    have he : U.ι ⁻¹ᵁ E.curve.hom.smoothLocus = ⊤ := by
      rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    exact he.ge (show (⟨x, hx⟩ : U) ∈ (⊤ : U.toScheme.Opens) from trivial)
  let j := Scheme.homOfLE E.curve.left hU
  have hj : j ≫ E.curve.hom.smoothLocus.ι = U.ι := by simp [j]
  rw [← hj, Category.assoc]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1)
    E.smoothOpen_relativeDimension j

end FLT.Mazur.GeneralizedEllipticCurve
