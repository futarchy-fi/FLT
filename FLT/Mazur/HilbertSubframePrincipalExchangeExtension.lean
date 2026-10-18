/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeOriginalLocalization
public import FLT.Mazur.SchemeInvariantPrincipalRelationLifts

/-!
# Extending principal exchange solutions to independent affine targets

A solution on a principal target chart cut out by an ORIGINAL scalar gives an
actual boundary-kernel correction on the unchanged affine target. Powers of
that same scalar clear the boundary and exchange equations; if it belongs to
the original multiplicative set, the exact localized obstruction vanishes.
Existence of such a principal solution near every original prime remains open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "E" => (pullOpen eo W).val

variable (m' : ℕ) (a : Fin m')
  (U' : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin m'),
    (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ U' = U')
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
local notation "Tinv" => invariantCoordinates (restrictedAction
  (normalizedFullRelationAction f hL d V c k m' a) U' hU')

variable (h : ∀ ι : Fin m' ↪ Fin n,
    U ≤ subframeMap (fullRelationSchemeEquivalence f hL d V c k) o a ι ⁻¹ᵁ U')
  (ι : Fin m' ↪ Fin n) (b₀ : Fin n)
local notation "β" => normalizedOriginalBoundaryHom f hL d V c k m' a W U' hU' hU'W
local notation "δ" => originalSubframeExchangeLinearMap
  f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀
local notation "Btarget" => invariantCoordinates (boundaryOpenAction
  (normalizedOriginalBoundaryAction f hL d V c k m' a)
  (normalizedFullRelationAction f hL d V c k m' a)
  (normalizedOriginalBoundaryInclusion f hL d V c k m' a)
  (normalizedOriginalBoundaryAction_inclusion f hL d V c k m' a) U' hU')

local notation "K" => originalScalarExchangeCorrections
  f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀
local notation "σS" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σT" => normalizedOriginalScalarMap f hL d V c k m' a W U' hU' hU'W
local notation "β₀" => normalizedBoundaryChartMap f hL d V c k m' a U' hU'
local notation "δ₀" => subframeExchangeMap e o a U U' hU' h ι b₀
variable (M : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))

attribute [local irreducible] normalizedOriginalScalarMap originalLocalizedExchangeClass
  originalScalarExchangeCorrections originalSubframeExchangeLinearMap

variable (ha : IsAffineOpen U) (ha' : IsAffineOpen U')
local notation "τT" => restrictedAction
  (normalizedFullRelationAction f hL d V c k m' a) U' hU'
local notation "jT" => (normalizedOriginalBoundaryInclusion f hL d V c k m' a) ∣_ U'
local notation "F" => subframeRefinementMap e o a
  (ι.trans (Equiv.swap (ι a) b₀).toEmbedding) U U' (h _)
local notation "G" => subframeRefinementMap e o a ι U U' (h ι)

omit [Etale V.hom] in
include hU hUW in
/-- The two actual selections pull back every original scalar identically. -/
theorem originalPrincipalExchange_scalar (x : Ω) :
    (F).appTop (σT x).val = (G).appTop (σT x).val := by
  simp only [normalizedOriginalScalarMap_subframe f hL d V c k n o W U hU hUW
    m' a U' hU' hU'W]

local notation "hscalar" => originalPrincipalExchange_scalar
  f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀

include ha ha' in
/-- A principal solution clears to the fixed target using an original denominator power. -/
theorem originalPrincipalExchange_correction (x : Ω) (u : Tinv)
    (v : invariantCoordinates (principalAction τT (σT x)))
    (hb : (principalPullbackMap jT (σT x).val).appTop v.val =
      (((normalizedOriginalBoundaryInclusion f hL d V c k m' a) ⁻¹ᵁ U').toScheme.basicOpen
        ((jT).appTop (σT x).val)).ι.appTop ((jT).appTop u.val))
    (he : (principalPullbackMap F (σT x).val).appTop v.val =
      (principalPairSecond F G (σT x).val (hscalar x)).appTop v.val) :
    ∃ (l : ℕ) (w : Tinv), β₀ w = 0 ∧ δ₀ w = (σS x).val ^ l * δ₀ u := by
  let _ : IsAffine U.toScheme := ha
  let _ : IsAffine U'.toScheme := ha'
  let _ := isAffine_of_isAffineHom jT
  obtain ⟨l, w, hw, hd⟩ := principal_invariant_relation_correction jT τT (σT x)
    (fun _ : Unit ↦ F) (fun _ : Unit ↦ G) (fun _ ↦ hscalar x) v u hb (fun _ ↦ he)
  refine ⟨l, w, Subtype.ext hw, ?_⟩
  have hd' := hd ()
  simpa only [normalizedOriginalScalarMap_subframe f hL d V c k n o W U hU hUW
    m' a U' hU' hU'W, subframeExchangeMap, subframeSelectionDifference,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hd'

include ha ha' in
/-- Original multiplicative denominators turn a principal solution into local exchange vanishing. -/
theorem originalLocalizedExchangeClass_principal_zero (x : M) (u : Tinv)
    (v : invariantCoordinates (principalAction τT (σT x.val)))
    (hb : (principalPullbackMap jT (σT x.val).val).appTop v.val =
      (((normalizedOriginalBoundaryInclusion f hL d V c k m' a) ⁻¹ᵁ U').toScheme.basicOpen
        ((jT).appTop (σT x.val).val)).ι.appTop ((jT).appTop u.val))
    (he : (principalPullbackMap F (σT x.val).val).appTop v.val =
      (principalPairSecond F G (σT x.val).val (hscalar x.val)).appTop v.val) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ M u = 0 := by
  obtain ⟨l, w, hw, hd⟩ := originalPrincipalExchange_correction
    f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀ ha ha' x.val u v hb he
  rw [originalLocalizedExchangeClass_zero_iff]
  refine ⟨x ^ l, w, hw, ?_⟩
  simpa only [SubmonoidClass.coe_pow, map_pow, Subring.coe_pow] using hd

end FLT.Mazur.HilbertChart.AffineRestriction
