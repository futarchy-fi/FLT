/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberInterior
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Closed original relations give clopen full-envelope regions

For a universally closed translation, the full-fiber locus is open. If the
original second endpoint is universally closed and the translation is affine
etale, the missing-envelope image is also open. Thus the actual full-fiber
region is clopen. No initial fullness or nonzero coefficient is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

omit [Algebra.FiniteType ℤ R] [IsAffine V.left] in
/-- The independent envelope projection is open for the original etale translation. -/
theorem fullEnvelopeProjection_isOpenMap : IsOpenMap π := by
  let _ : Etale π := MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip
    (inferInstanceAs (Etale V.hom))
  exact (π).isOpenMap

variable [UniversallyClosed (snd f hL d V c k).left]

omit [Etale V.hom] [IsOpenImmersion k.left] in
/-- Closedness of the original endpoint makes the actual open envelope image closed. -/
theorem toEnvelope_isClosedMap : IsClosedMap j := by
  let _ : IsSeparated π := MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip
    (inferInstanceAs (IsSeparated V.hom))
  let _ : UniversallyClosed (j ≫ π) := by
    rw [← Over.comp_left, toEnvelope_test]
    infer_instance
  let _ : UniversallyClosed j := UniversallyClosed.of_comp_of_isSeparated j π
  exact (j).isClosedMap

/-- All missing independent branches have an open image in the original source. -/
theorem fullEnvelopeLocus_isClosed : IsClosed (fullEnvelopeLocus f hL d V c k) := by
  change IsClosed (π '' ((j).opensRange : Set (prod A V).left)ᶜ)ᶜ
  apply IsOpen.isClosed_compl
  apply fullEnvelopeProjection_isOpenMap V
  exact (toEnvelope_isClosedMap f hL d V c k).isClosed_range.isOpen_compl

variable [UniversallyClosed V.hom]

/-- The constructed full independent-fiber locus is clopen, even for nonsplit translations. -/
theorem fullEnvelopeLocus_isClopen : IsClopen (fullEnvelopeLocus f hL d V c k) :=
  ⟨fullEnvelopeLocus_isClosed f hL d V c k,
    (fullEnvelopeOpen f hL d V c k (fullEnvelopeProjection_isClosedMap V)).isOpen⟩

/-- Closedness of the good interior is derived from original endpoint geometry. -/
theorem fullEnvelopeInterior_isClosed :
    IsClosed (fullEnvelopeInterior f hL d V c k : Set A.left) := by
  rw [fullEnvelopeInterior_coe, (fullEnvelopeLocus_isClopen f hL d V c k).isOpen.interior_eq]
  exact fullEnvelopeLocus_isClosed f hL d V c k

/-- In this geometric case no full-fiber point is lost on taking the interior. -/
theorem fullEnvelopeInterior_eq_locus :
    (fullEnvelopeInterior f hL d V c k : Set A.left) = fullEnvelopeLocus f hL d V c k :=
  (fullEnvelopeLocus_isClopen f hL d V c k).isOpen.interior_eq

end FLT.Mazur.HilbertChart.AffineRestriction
