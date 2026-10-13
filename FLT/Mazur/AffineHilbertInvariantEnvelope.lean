/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationOperations
public import FLT.Mazur.SchemeRelationInvariantEnvelope
public import FLT.Mazur.SchemeOpenEnvelopeDenominators
public import FLT.Mazur.SchemeRelationIsoInvariants

/-!
# Original invariant denominators and full restricted tensor envelopes

The admissible coefficients form a constructed radical ideal in the ORIGINAL
invariant ring. Each member gives an invariant principal source open whose
full double relation is the entire envelope over that open. No covering or
nonvanishing denominator is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections SchemeOpenEnvelope
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
local notation "C" => compatibleFunctions (Over.Hom.left p) (Over.Hom.left q)

/-- Admissible invariant source coefficients are tested on the whole original tensor envelope. -/
def invariantEnvelopeDenominators : Ideal C :=
  denominatorIdeal ((π).appTop.hom.comp (C).subtype) (j).opensRange

/-- Membership means that every independent translation over the principal source is present. -/
theorem mem_invariantEnvelopeDenominators (r : C) :
    r ∈ invariantEnvelopeDenominators f hL d V c k ↔
      (π) ⁻¹ᵁ A.left.basicOpen r.val ≤ (j).opensRange := by
  change (prod A V).left.basicOpen ((π).appTop r.val) ≤ (j).opensRange ↔ _
  rw [Scheme.Hom.preimage_basicOpen_top]

/-- Powers introduce no new principal neighborhoods, so the actual admissible ideal is radical. -/
theorem invariantEnvelopeDenominators_isRadical :
    (invariantEnvelopeDenominators f hL d V c k).IsRadical :=
  denominatorIdeal_isRadical _ _

/-- The unit ideal detects the actual full original envelope, rather than assuming it. -/
theorem invariantEnvelopeDenominators_eq_top_iff :
    invariantEnvelopeDenominators f hL d V c k = ⊤ ↔ IsIso j :=
  denominatorIdeal_eq_top_iff_isIso _ _

/-- Every actual admissible coefficient gives the FULL original relation on its source open. -/
def invariantPrincipalEnvelopeIso (r : C)
    (hr : r ∈ invariantEnvelopeDenominators f hL d V c k) :
    SchemeRelationRestriction.doubleDomain (p).left (q).left (A.left.basicOpen r.val).ι ≅
      ((π) ⁻¹ᵁ A.left.basicOpen r.val).toScheme :=
  SchemeRelationRestriction.invariantEnvelopeIso (p).left (q).left j π
    (congrArg Over.Hom.left (toEnvelope_test f hL d V c k)) (A.left.basicOpen r.val)
    (compatibleFunctions_basicOpen _ _ r)
    ((mem_invariantEnvelopeDenominators f hL d V c k r).mp hr)

/-- The constructed isomorphism retains the original full relation arrow into its envelope. -/
@[reassoc]
theorem invariantPrincipalEnvelopeIso_hom_ι (r : C)
    (hr : r ∈ invariantEnvelopeDenominators f hL d V c k) :
    (invariantPrincipalEnvelopeIso f hL d V c k r hr).hom ≫
        ((π) ⁻¹ᵁ A.left.basicOpen r.val).ι =
      SchemeRelationRestriction.arrow (p).left (q).left (A.left.basicOpen r.val).ι ≫ j :=
  SchemeRelationRestriction.invariantEnvelopeIso_hom_ι _ _ _ _ _ _ _ _

omit [IsOpenImmersion k.left] in
/-- These constructed source domains are invariant affine opens whenever the source is affine. -/
theorem invariantPrincipalEnvelope_source [IsAffine A.left] (r : C) :
    IsAffineOpen (A.left.basicOpen r.val) ∧
      (p).left ⁻¹ᵁ A.left.basicOpen r.val = (q).left ⁻¹ᵁ A.left.basicOpen r.val :=
  ⟨compatibleFunctions_basicOpen_affine _ _ r, compatibleFunctions_basicOpen _ _ r⟩

end FLT.Mazur.HilbertChart.AffineRestriction
