/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberPrincipal
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Retained affine principal points have open envelopes for finite translations

On a finite translation branch, the whole-orbit principal restriction retains
an actual open full-envelope neighborhood of the chosen point. The result
applies to the proper family over its changed coefficient base. Transport of
an original chart and its full fiber to that changed family is separate work.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsFinite V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]

/-- On finite translation branches every full fiber already has an open full-envelope domain. -/
theorem fullEnvelopeLocus_eq_interior_of_finite :
    fullEnvelopeLocus f hL d V c k = (fullEnvelopeInterior f hL d V c k : Set A.left) := by
  rw [fullEnvelopeInterior_eq_fullEnvelopeOpen f hL d V c k
    (fullEnvelopeProjection_isClosedMap V)]
  rfl

variable [IsAffine A.left] [IsAffine V.left] [Etale V.hom]

/-- The constructed principal source retains the point in its NEW full-fiber interior. -/
theorem exists_finite_fullFiber_principal_interior (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) :
    ∃ (r : Γ(A.left, ⊤)) (hr : x ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨x, hr⟩ : (A.left.basicOpen r).toScheme) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) := by
  have hx' : x ∈ fullEnvelopeInterior f hL d V c k :=
    (Set.ext_iff.mp (fullEnvelopeLocus_eq_interior_of_finite f hL d V c k) x).mp hx
  obtain ⟨r, hr, hsub, hgood⟩ := exists_fullInterior_principal_chart f hL d V c k x hx'
  refine ⟨r, hr, hsub, ?_⟩
  exact (Set.ext_iff.mp (fullEnvelopeLocus_eq_interior_of_finite f hL d V c
    (orbitPrincipalChart f d V k r)) ⟨x, hr⟩).mp hgood

/-- In particular the NEW open domain on the constructed affine source is nonempty. -/
theorem exists_finite_principal_nonempty_interior (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) :
    ∃ r : Γ(A.left, ⊤),
      (fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) :
        Set (orbitPrincipalSource r).left).Nonempty := by
  obtain ⟨r, hr, _, hgood⟩ := exists_finite_fullFiber_principal_interior f hL d V c k x hx
  exact ⟨r, ⟨x, hr⟩, hgood⟩

end FLT.Mazur.HilbertChart.AffineRestriction
