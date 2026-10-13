/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberInvariant
public import FLT.Mazur.AffineHilbertInvariantEnvelope
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Constructed invariant full-envelope opens for closed translation projections

The missing-envelope image gives a concrete invariant open. Universally closed
translations, including finite translations, supply the required closedness.
Prime avoidance gives source coefficients on this locus; their invariance is
not inferred from the invariance of their supporting open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

omit [Algebra.FiniteType ℤ R] in
/-- A universally closed translation makes the actual independent envelope projection closed. -/
theorem fullEnvelopeProjection_isClosedMap [UniversallyClosed V.hom] : IsClosedMap π := by
  let _ : UniversallyClosed π := MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip
    (inferInstanceAs (UniversallyClosed V.hom))
  exact (π).isClosedMap

variable (hπ : IsClosedMap (Over.Hom.left (prod.fst : prod A V ⟶ A)))

/-- The actual open obtained by removing the image of the missing original envelope. -/
def fullEnvelopeOpen : A.left.Opens := fullFiberOpen π (j).opensRange hπ

/-- Its underlying set is exactly the previously constructed full-fiber locus. -/
theorem fullEnvelopeOpen_coe :
    (fullEnvelopeOpen f hL d V c k hπ : Set A.left) =
      fullEnvelopeLocus f hL d V c k := rfl

/-- Both ORIGINAL endpoints preserve this constructed open. -/
theorem fullEnvelopeOpen_invariant :
    (p).left ⁻¹ᵁ fullEnvelopeOpen f hL d V c k hπ =
      (q).left ⁻¹ᵁ fullEnvelopeOpen f hL d V c k hπ := by
  apply SetLike.coe_injective
  exact fullEnvelopeLocus_invariant f hL d V c k

/-- The entire independent envelope over this source open lies in the original relation. -/
theorem fullEnvelopeOpen_full :
    (π) ⁻¹ᵁ fullEnvelopeOpen f hL d V c k hπ ≤ (j).opensRange :=
  preimage_fullFiberOpen_le π (j).opensRange hπ

/-- Original admissibility means precisely support in the constructed full-envelope open. -/
theorem invariantDenominator_iff_fullEnvelopeOpen
    (r : compatibleFunctions (p).left (q).left) :
    r ∈ invariantEnvelopeDenominators f hL d V c k ↔
      A.left.basicOpen r.val ≤ fullEnvelopeOpen f hL d V c k hπ := by
  rw [mem_invariantEnvelopeDenominators]
  exact (subset_fullFiberLocus_iff π (j).opensRange (A.left.basicOpen r.val)).symm

include hπ in
/-- A finite collection of full fibers gives a nonvanishing coefficient of the actual source. -/
theorem exists_fullEnvelope_source_coefficient [IsAffine A.left]
    (s : Set A.left) (hs : s.Finite) (hgood : s ⊆ fullEnvelopeLocus f hL d V c k) :
    ∃ r : Γ(A.left, ⊤), s ⊆ A.left.basicOpen r ∧
      (π) ⁻¹ᵁ A.left.basicOpen r ≤ (j).opensRange := by
  obtain ⟨r, hr, h⟩ := exists_fullFiber_coefficient π (j).opensRange hπ s hs hgood
  refine ⟨r, hr, ?_⟩
  change (prod A V).left.basicOpen ((π).appTop r) ≤ (j).opensRange at h
  rwa [← Scheme.Hom.preimage_basicOpen_top] at h

/-- The FULL original double relation is already effective over this constructed open. -/
def fullEnvelopeOpenRelationIso :
    SchemeRelationRestriction.doubleDomain (p).left (q).left
        (fullEnvelopeOpen f hL d V c k hπ).ι ≅
      ((π) ⁻¹ᵁ fullEnvelopeOpen f hL d V c k hπ).toScheme :=
  SchemeRelationRestriction.invariantEnvelopeIso (p).left (q).left j π
    (congrArg Over.Hom.left (toEnvelope_test f hL d V c k))
    (fullEnvelopeOpen f hL d V c k hπ) (fullEnvelopeOpen_invariant f hL d V c k hπ)
    (fullEnvelopeOpen_full f hL d V c k hπ)

/-- The constructed full-relation isomorphism retains its original envelope arrow. -/
@[reassoc]
theorem fullEnvelopeOpenRelationIso_hom_ι :
    (fullEnvelopeOpenRelationIso f hL d V c k hπ).hom ≫
        ((π) ⁻¹ᵁ fullEnvelopeOpen f hL d V c k hπ).ι =
      SchemeRelationRestriction.arrow (p).left (q).left
        (fullEnvelopeOpen f hL d V c k hπ).ι ≫ j :=
  SchemeRelationRestriction.invariantEnvelopeIso_hom_ι _ _ _ _ _ _ _ _

end FLT.Mazur.HilbertChart.AffineRestriction
