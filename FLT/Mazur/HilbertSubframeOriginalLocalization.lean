/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeScalarObstruction
public import FLT.Mazur.BoundaryExchangeLocalization
public import FLT.Mazur.HilbertBoundaryPrincipalLifting

/-!
# Exact exchange localization at original boundary source primes

The correction quotient is localized over the original invariant ring. Its
zero test clears an original denominator and constructs a genuine target
boundary-kernel correction. Original boundary source primes supply the actual
prime complements; this is not localization at integer primes.
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

/-- The actual class localized at any original scalar multiplicative set. -/
def originalLocalizedExchangeClass :
    let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
    let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
    Tinv →ₗ[Ω] LocalizedModule M (Γ(U.toScheme, ⊤) ⧸ K) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryExchangeObstruction.localizedLiftClass (β).toLinearMap δ M

/-- Vanishing clears an original denominator into the actual target correction image. -/
theorem originalLocalizedExchangeClass_zero_iff (v : Tinv) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ M v = 0 ↔
        ∃ x : M, ∃ zeta : Tinv, β₀ zeta = 0 ∧ δ₀ zeta = (σS x.val).val * δ₀ v := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryExchangeObstruction.localizedLiftClass_zero_iff (β).toLinearMap δ M v

/-- The same local criterion produces an exchange-free target lift after scaling. -/
theorem originalLocalizedExchangeClass_zero_iff_lift (v : Tinv) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ M v = 0 ↔
        ∃ x : M, ∃ w : Tinv, β₀ w = β₀ (σT x.val) * β₀ v ∧ δ₀ w = 0 := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryExchangeObstruction.localizedLiftClass_zero_iff_lift (β).toLinearMap δ M v

local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

/-- Prime denominators come from the unchanged original boundary source ring. -/
def originalSubframePrimeDenominators (P : Ideal Tsource) [P.IsPrime] : Submonoid Ω :=
  (P.comap κ).primeCompl

/-- Clearing the local class at an original source prime gives a scalar outside that prime. -/
theorem originalLocalizedExchangeClass_prime_zero_iff
    (P : Ideal Tsource) [P.IsPrime] (v : Tinv) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ (originalSubframePrimeDenominators f hL d V c k W P) v = 0 ↔
      ∃ x : Ω, κ x ∉ P ∧ ∃ zeta : Tinv,
        β₀ zeta = 0 ∧ δ₀ zeta = (σS x).val * δ₀ v := by
  rw [originalLocalizedExchangeClass_zero_iff]
  constructor
  · rintro ⟨x, zeta, hz, hd⟩
    exact ⟨x.val, x.property, zeta, hz, hd⟩
  · rintro ⟨x, hx, zeta, hz, hd⟩
    exact ⟨⟨x, hx⟩, zeta, hz, hd⟩

end FLT.Mazur.HilbertChart.AffineRestriction
