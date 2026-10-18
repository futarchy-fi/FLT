/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeOpenImagePrimeCorrections

public import FLT.Mazur.SchemeAffineBadComplementIntegral

/-!
# Fixed Hilbert target corrections from constructed bad quotients

The affine target has a canonical bad-complement scheme. Integrality only
of its quotient coordinates, together with containment of the whole original
fiber in the usable open, supplies the original denominator used by the
existing exchange class. The compatible lift on the usable open is still
required; this does not assert unconditional original local vanishing.
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

local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)
local notation "σ₀" => invariantScalarCoordinates τT σT
variable (O : U'.toScheme.Opens)
  (hO : ∀ g : Equiv.Perm (Fin m'),
    (restrictedAction (normalizedFullRelationAction f hL d V c k m' a) U' hU' g).hom ⁻¹ᵁ O = O)
  (FO GO : U.toScheme ⟶ O.toScheme)
  (hF : FO ≫ O.ι = subframeRefinementMap (fullRelationSchemeEquivalence f hL d V c k)
    o a (ι.trans (Equiv.swap (ι a) b₀).toEmbedding) U U' (h _))
  (hG : GO ≫ O.ι = subframeRefinementMap (fullRelationSchemeEquivalence f hL d V c k)
    o a ι U U' (h ι))

include ha ha' hU hUW hO hF hG in
/-- Integral bad quotient coordinates replace the original-prime avoidance assumption. -/
theorem originalLocalizedExchangeClass_bad_quotient_prime_zero
    (J : Ideal Γ(U'.toScheme, ⊤))
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(U'.toScheme, ⊤)) =
      U'.toScheme.toSpecΓ '' (O : Set U'.toScheme)ᶜ)
    (hInt : ((Ideal.Quotient.mk J).comp σ₀).IsIntegral)
    (P : Ideal Tsource) [P.IsPrime]
    (hP : ∀ x : U'.toScheme,
      SchemeScalarPrincipalNeighborhood.scalarMorphism σ₀ x =
        PrimeSpectrum.comap κ ⟨P, inferInstance⟩ → x ∈ O)
    (v : invariantCoordinates (restrictedAction τT O hO)) (u : Tinv)
    (hb : ((jT) ∣_ O).appTop v.val = ((jT) ⁻¹ᵁ O).ι.appTop ((jT).appTop u.val))
    (he : FO.appTop v.val = GO.appTop v.val) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀
        (originalSubframePrimeDenominators f hL d V c k W P) u = 0 := by
  let _ : IsAffine U'.toScheme := ha'
  have hSafe :=
    SchemeScalarPrincipalNeighborhood.mem_scalarNeighborhoodLocus_of_badQuotient_integral
    σ₀ J O hJ hInt (PrimeSpectrum.comap κ ⟨P, inferInstance⟩) hP
  exact originalLocalizedExchangeClass_open_image_prime_zero
    f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀
    ha ha' O hO FO GO hF hG P hSafe v u hb he

end FLT.Mazur.HilbertChart.AffineRestriction
