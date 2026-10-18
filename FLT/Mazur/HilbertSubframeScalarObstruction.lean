/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeScalarLinearMaps
public import FLT.Mazur.HilbertSubframeBoundaryExchangeMap

/-!
# The exact subframe correction obstruction over original scalars

The actual target boundary kernel and exchange define an original-scalar
submodule. Its zero class is precisely the previous additive criterion, so
changing scalars does not enlarge the available corrections. Affine target
surjectivity also gives a linear operator on the actual boundary ring.
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

/-- Exchanges of the exact target boundary kernel, over the original scalar ring. -/
def originalScalarExchangeCorrections :
    let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
    Submodule Ω Γ(U.toScheme, ⊤) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryExchangeObstruction.correctionImage (β).toLinearMap δ

local notation "K" => originalScalarExchangeCorrections
  f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀

/-- The exact original exchange class is linear over original scalars. -/
def originalScalarExchangeClass :
    let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
    let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
    Tinv →ₗ[Ω] (Γ(U.toScheme, ⊤) ⧸ K) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryExchangeObstruction.liftClass (β).toLinearMap δ

/-- Original scalars preserve exactly the old correction image as a set. -/
theorem originalScalarExchangeCorrections_mem (x : Γ(U.toScheme, ⊤)) :
    x ∈ K ↔ x ∈ originalSubframeExchangeCorrectionImage
      f hL d V c k n o U m' a U' hU' h ι b₀ := Iff.rfl

/-- No new solutions are introduced by the upgrade from integer to original scalars. -/
theorem originalScalarExchangeClass_zero_iff (v : Tinv) :
    originalScalarExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ v = 0 ↔
        originalSubframeExchangeClass f hL d V c k n o U m' a U' hU' h ι b₀ v = 0 := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  rw [originalSubframeExchangeClass_zero_iff]
  exact BoundaryExchangeObstruction.liftClass_zero_iff (β).toLinearMap δ v

/-- Independent target lifts give the same original-scalar class. -/
theorem originalScalarExchangeClass_independent (v w : Tinv)
    (hv : normalizedBoundaryChartMap f hL d V c k m' a U' hU' v =
      normalizedBoundaryChartMap f hL d V c k m' a U' hU' w) :
    originalScalarExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ v =
    originalScalarExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ w := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryExchangeObstruction.liftClass_eq_of_boundary_eq (β).toLinearMap δ v w hv

/-- The affine target induces a canonical boundary obstruction over original scalars. -/
def originalScalarBoundaryExchangeMap (ha' : IsAffineOpen U') :
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
    let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
    Btarget →ₗ[Ω] (Γ(U.toScheme, ⊤) ⧸ K) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryExchangeObstruction.boundaryMap (β).toLinearMap δ
    (normalizedBoundaryChartMap_surjective f hL d V c k m' a U' hU' ha')

/-- Any exact target lift computes this original-scalar boundary obstruction. -/
theorem originalScalarBoundaryExchangeMap_apply (ha' : IsAffineOpen U') (v : Tinv) :
    originalScalarBoundaryExchangeMap f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ ha' (β v) =
    originalScalarExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ v := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact BoundaryExchangeObstruction.boundaryMap_apply (β).toLinearMap δ _ v

end FLT.Mazur.HilbertChart.AffineRestriction
