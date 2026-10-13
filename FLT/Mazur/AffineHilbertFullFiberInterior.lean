/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberOpen
public import FLT.Mazur.AffineHilbertRelationNeighborhoods
public import FLT.Mazur.SchemeOpenEnvelopeInterior

/-!
# Maximal invariant full-envelope opens for general etale translations

Taking the interior removes the closed-projection requirement. Both original
etale endpoints preserve this open, and its full restricted relation fills the
independent envelope. The open need not be affine, nonempty, or covering.
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

/-- The largest open source with a full original independent envelope. -/
def fullEnvelopeInterior : A.left.Opens := fullFiberInterior π (j).opensRange

/-- The underlying set is the interior of the original full-fiber locus. -/
theorem fullEnvelopeInterior_coe :
    (fullEnvelopeInterior f hL d V c k : Set A.left) =
      interior (fullEnvelopeLocus f hL d V c k) := rfl

/-- The entire independent envelope over the constructed open is present. -/
theorem fullEnvelopeInterior_full :
    (π) ⁻¹ᵁ fullEnvelopeInterior f hL d V c k ≤ (j).opensRange :=
  preimage_fullFiberInterior_le π (j).opensRange

/-- Every actual open full-envelope source factors through this largest one. -/
theorem le_fullEnvelopeInterior_iff (U : A.left.Opens) :
    U ≤ fullEnvelopeInterior f hL d V c k ↔ (π) ⁻¹ᵁ U ≤ (j).opensRange :=
  le_fullFiberInterior_iff π (j).opensRange U

/-- Original invariant admissibility is detected by support in the constructed interior. -/
theorem invariantDenominator_iff_fullEnvelopeInterior
    (r : compatibleFunctions (p).left (q).left) :
    r ∈ invariantEnvelopeDenominators f hL d V c k ↔
      A.left.basicOpen r.val ≤ fullEnvelopeInterior f hL d V c k := by
  rw [mem_invariantEnvelopeDenominators, le_fullEnvelopeInterior_iff]

/-- The new construction agrees with the previous one when the projection is closed. -/
theorem fullEnvelopeInterior_eq_fullEnvelopeOpen (hπ : IsClosedMap π) :
    fullEnvelopeInterior f hL d V c k = fullEnvelopeOpen f hL d V c k hπ :=
  fullFiberInterior_eq_fullFiberOpen π (j).opensRange hπ

variable [Etale V.hom]

/-- General etale translations suffice for invariance of the maximal open full-fiber source. -/
theorem fullEnvelopeInterior_invariant :
    (p).left ⁻¹ᵁ fullEnvelopeInterior f hL d V c k =
      (q).left ⁻¹ᵁ fullEnvelopeInterior f hL d V c k :=
  fullFiberInterior_invariant π (j).opensRange (p).left (q).left
    (p).left.isOpenMap (q).left.isOpenMap (fullEnvelopeLocus_invariant f hL d V c k)

/-- The ORIGINAL full relation over the constructed open fills its independent envelope. -/
def fullEnvelopeInteriorRelationIso :
    SchemeRelationRestriction.doubleDomain (p).left (q).left
        (fullEnvelopeInterior f hL d V c k).ι ≅
      ((π) ⁻¹ᵁ fullEnvelopeInterior f hL d V c k).toScheme :=
  SchemeRelationRestriction.invariantEnvelopeIso (p).left (q).left j π
    (congrArg Over.Hom.left (toEnvelope_test f hL d V c k))
    (fullEnvelopeInterior f hL d V c k) (fullEnvelopeInterior_invariant f hL d V c k)
    (fullEnvelopeInterior_full f hL d V c k)

/-- The full-relation isomorphism retains the actual original envelope arrow. -/
@[reassoc]
theorem fullEnvelopeInteriorRelationIso_hom_ι :
    (fullEnvelopeInteriorRelationIso f hL d V c k).hom ≫
        ((π) ⁻¹ᵁ fullEnvelopeInterior f hL d V c k).ι =
      SchemeRelationRestriction.arrow (p).left (q).left
        (fullEnvelopeInterior f hL d V c k).ι ≫ j :=
  SchemeRelationRestriction.invariantEnvelopeIso_hom_ι _ _ _ _ _ _ _ _

end FLT.Mazur.HilbertChart.AffineRestriction
