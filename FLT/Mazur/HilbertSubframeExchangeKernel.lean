/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeExchangeObstruction
public import FLT.Mazur.EquivalenceRelationBoundarySubframeKernel

/-!
# The exact exchange obstruction inside the original source boundary kernel

Available target corrections lie in the actual unreduced source boundary kernel.
Its quotient by those corrections injects into the ambient exchange quotient.
Thus the original error can be studied in the boundary kernel without losing
or introducing solutions. No finiteness or local annihilation is inferred.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

variable (m' : ℕ) (a : Fin m')
  (U' : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin m'),
    (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ U' = U')
  (h : ∀ ι : Fin m' ↪ Fin n,
    U ≤ subframeMap (fullRelationSchemeEquivalence f hL d V c k) o a ι ⁻¹ᵁ U')
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

variable (ι : Fin m' ↪ Fin n) (b₀ : Fin n)
local notation "Tinv" => invariantCoordinates (restrictedAction
  (normalizedFullRelationAction f hL d V c k m' a) U' hU')
local notation "β" => normalizedBoundaryChartMap f hL d V c k m' a U' hU'
local notation "δ" => subframeExchangeMap e o a U U' hU' h ι b₀

local notation "βS" => ((j) ∣_ U).appTop.hom.toAddMonoidHom.toIntLinearMap
local notation "Ksource" => LinearMap.ker βS
local notation "Kimage" => originalSubframeExchangeCorrectionImage
  f hL d V c k n o U m' a U' hU' h ι b₀

/-- All available target corrections lie in the actual unreduced source boundary kernel. -/
theorem originalSubframeExchangeCorrectionImage_le : Kimage ≤ Ksource := by
  rintro x ⟨v, hv, rfl⟩
  change ((j) ∣_ U).appTop (δ v) = 0
  apply InvariantBoundary.subframeExchangeMap_boundary_zero
    e o a i z r s hr hs U U' hU' h ι b₀ v
  exact congrArg Subtype.val hv

/-- The same actual corrections regarded as elements of the original source boundary kernel. -/
def originalSubframeKernelCorrections : Submodule ℤ Ksource :=
  (Kimage).comap (Ksource).subtype

local notation "Kinside" => originalSubframeKernelCorrections
  f hL d V c k n o U m' a U' hU' h ι b₀

/-- Inclusion of the source boundary kernel induces the exact exchange quotient comparison. -/
def originalSubframeKernelQuotientInclusion :
    (Ksource ⧸ Kinside) →ₗ[ℤ] (Γ(U.toScheme, ⊤) ⧸ Kimage) :=
  (Kinside).mapQ Kimage (Ksource).subtype le_rfl

/-- No source boundary-kernel obstruction is lost by passing to the ambient exchange quotient. -/
theorem originalSubframeKernelQuotientInclusion_injective :
    Function.Injective
      (originalSubframeKernelQuotientInclusion f hL d V c k n o U m' a U' hU' h ι b₀) := by
  change Function.Injective ((Kinside).mapQ Kimage (Ksource).subtype le_rfl)
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mapQ]
  exact Submodule.mkQ_map_self _

/-- The original exchange error is an element of the actual source boundary-kernel quotient. -/
def originalSubframeKernelExchangeClass (v : Tinv)
    (hv : β v = normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t) :
    Ksource ⧸ Kinside :=
  (Kinside).mkQ ⟨δ v, normalizedOrbitBoundary_subframeExchange_zero
    f hL d V c k n o W U hU hUW m' a U' hU' h hU'W t ι b₀ v hv⟩

/-- The kernel class is exactly the original ambient exchange class under the inclusion. -/
theorem originalSubframeKernelExchangeClass_image (v : Tinv)
    (hv : β v = normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t) :
    originalSubframeKernelQuotientInclusion f hL d V c k n o U m' a U' hU' h ι b₀
      (originalSubframeKernelExchangeClass f hL d V c k n o W U hU hUW
        m' a U' hU' h hU'W t ι b₀ v hv) =
      originalSubframeExchangeClass f hL d V c k n o U m' a U' hU' h ι b₀ v := rfl

/-- Vanishing in the boundary kernel is precisely vanishing of the actual target obstruction. -/
theorem originalSubframeKernelExchangeClass_zero_iff (v : Tinv)
    (hv : β v = normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t) :
    originalSubframeKernelExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' h hU'W t ι b₀ v hv = 0 ↔
      originalSubframeExchangeClass f hL d V c k n o U m' a U' hU' h ι b₀ v = 0 := by
  rw [← (originalSubframeKernelQuotientInclusion_injective
    f hL d V c k n o U m' a U' hU' h ι b₀).eq_iff,
    map_zero, originalSubframeKernelExchangeClass_image]

end FLT.Mazur.HilbertChart.AffineRestriction
