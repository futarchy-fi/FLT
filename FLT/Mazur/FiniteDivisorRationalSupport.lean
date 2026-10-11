/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralCurveCartierFinite
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Rational points at every point of a finite divisor

Every support point of a finite closed subscheme over an algebraically closed
field is the image of an actual rational section. The original closed subscheme
and its nonreduced structure are retained throughout.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.FCurve
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData)

/-- Each point of a finite closed subscheme is closed in the ambient scheme. -/
theorem finiteDivisor_isClosed_point [IsFinite (I.subschemeι ≫ f)]
    {x : X} (hx : x ∈ I.support) : IsClosed ({x} : Set X) := by
  obtain ⟨z, rfl⟩ := (I.range_subschemeι ▸ hx : x ∈ Set.range I.subschemeι)
  let _ : IsLocallyArtinian I.subscheme :=
    IsLocallyArtinian.of_locallyQuasiFinite (I.subschemeι ≫ f)
  simpa only [Set.image_singleton] using
    I.subschemeι.isClosedEmbedding.isClosedMap {z} isClosed_singleton

/-- Algebraic closedness supplies an actual rational section at every support point. -/
theorem finiteDivisor_exists_rationalPoint [IsAlgClosed k] [LocallyOfFiniteType f]
    [IsFinite (I.subschemeι ≫ f)] (x : X) (hx : x ∈ I.support) :
    ∃ p : Spec (.of k) ⟶ X, p ≫ f = 𝟙 _ ∧ p (IsLocalRing.closedPoint k) = x := by
  let hc := finiteDivisor_isClosed_point f I hx
  exact ⟨pointOfClosedPoint f x hc, pointOfClosedPoint_comp f x hc,
    pointOfClosedPoint_apply f x hc _⟩

end FLT.Mazur.FCurve
