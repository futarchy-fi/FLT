/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFullRelationOrderedPoints
public import FLT.Mazur.RelativeDistinctAffineEnvelope

/-!
# Stable affine neighborhoods in the full original ordered relation

Original inversion embeds the entire first-endpoint relation in the affine
product envelope. Applying the finite tuple construction gives actual stable
affine neighborhoods of every frame. Both original endpoints remain unchanged
on the frame scheme; this does not assert completeness on these neighborhoods.
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
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]

/-- The original affine envelope regarded over its actual source endpoint. -/
def firstRelationEnvelope : Over A.left := Over.mk (prod.fst : prod A V ⟶ A).left

/-- Inversion identifies the first-endpoint relation with an open of its affine envelope. -/
def firstRelationEnvelopeMap :
    fullRelationOverFirst f hL d V c k ⟶ firstRelationEnvelope V :=
  Over.homMk ((inverseSchemeIso f hL d V c k).hom ≫ (toEnvelope f hL d V c k).left) (by
    change (_ ≫ _) ≫ (prod.fst : prod A V ⟶ A).left = (fst f hL d V c k).left
    rw [Category.assoc, ← Over.comp_left, toEnvelope_test]
    exact congrArg Over.Hom.left (equivalence f hL d V c k).symmetry₂)

instance firstRelationEnvelope_affine : IsAffine (firstRelationEnvelope (A := A) V).left :=
  variableHilbertOverlap_envelope_affine V A

instance firstRelationEnvelopeMap_open :
    IsOpenImmersion (firstRelationEnvelopeMap f hL d V c k).left := by
  change IsOpenImmersion
    ((inverseSchemeIso f hL d V c k).hom ≫ (toEnvelope f hL d V c k).left)
  infer_instance

variable (n : ℕ)
open RelativeOrderedTuples
local notation "E" => fullRelationOverFirst f hL d V c k

/-- A genuine affine envelope for the entire original ordered-point scheme. -/
def fullRelationOrderedEnvelopeMap :
    (fullRelationOrderedPoints f hL d V c k n).left ⟶
      (tuples (firstRelationEnvelope (A := A) V) (Fin n)).left :=
  distinctEnvelopeMap (firstRelationEnvelopeMap f hL d V c k) n

instance fullRelationOrderedEnvelopeMap_open :
    IsOpenImmersion (fullRelationOrderedEnvelopeMap f hL d V c k n) :=
  inferInstanceAs (IsOpenImmersion
    (distinctEnvelopeMap (firstRelationEnvelopeMap f hL d V c k) n))

/-- Each original frame lies in an actual permutation-stable affine neighborhood. -/
theorem exists_fullRelation_ordered_stable_affine
    (x : (fullRelationOrderedPoints f hL d V c k n).left) :
    ∃ U : (fullRelationOrderedPoints f hL d V c k n).left.Opens,
      IsAffineOpen U ∧ x ∈ U ∧
        ∀ e : Equiv.Perm (Fin n), (fullRelationOrderedAction f hL d V c k n e).hom ⁻¹ᵁ U = U :=
  exists_distinct_orbit_affine (firstRelationEnvelopeMap f hL d V c k) n x

end FLT.Mazur.HilbertChart.AffineRestriction
