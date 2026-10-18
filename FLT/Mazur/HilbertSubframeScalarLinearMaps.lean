/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeOriginalScalars
public import FLT.Mazur.HilbertSubframeExchangeObstruction

/-!
# Actual selected pullbacks and exchange over original scalars

The independently chosen source and target use the same original invariant
section ring. The selected maps are algebra homomorphisms and their difference
is linear. The boundary map uses the induced original scalar action.
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

local notation "σS" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "Bsource" => invariantCoordinates (boundaryOpenAction ρ τ j hj U hU)

/-- The original section ring acts on the actual invariant chart ring. -/
@[instance_reducible]
def normalizedOriginalChartAlgebra : Algebra Ω Sinv := (σS).toAlgebra

/-- The same original scalars act on all functions of the source chart. -/
@[instance_reducible]
def normalizedOriginalRawAlgebra : Algebra Ω Γ(U.toScheme, ⊤) :=
  ((Subring.subtype _).comp σS).toAlgebra

/-- The exact boundary ring has its induced original scalar action. -/
@[instance_reducible]
def normalizedOriginalBoundaryAlgebra : Algebra Ω Bsource :=
  ((normalizedBoundaryChartMap f hL d V c k n o U hU).comp σS).toAlgebra

/-- The unchanged invariant boundary map as a map over the original ring. -/
def normalizedOriginalBoundaryHom :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Sinv →ₐ[Ω] Bsource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  exact
    { __ := normalizedBoundaryChartMap f hL d V c k n o U hU
      commutes' := fun _ ↦ rfl }

variable (m' : ℕ) (a : Fin m')
  (U' : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin m'),
    (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ U' = U')
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
local notation "Tinv" => invariantCoordinates (restrictedAction
  (normalizedFullRelationAction f hL d V c k m' a) U' hU')

/-- Each actual selected pullback is an algebra map for the original scalars. -/
def originalSubframePullbackHom (ι : Fin m' ↪ Fin n)
    (h : U ≤ subframeMap e o a ι ⁻¹ᵁ U') :
    let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
    let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
    Tinv →ₐ[Ω] Γ(U.toScheme, ⊤) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact
    { __ := (subframeRefinementMap e o a ι U U' h).appTop.hom.comp (Subring.subtype _)
      commutes' := fun x ↦ normalizedOriginalScalarMap_subframe
        f hL d V c k n o W U hU hUW m' a U' hU' hU'W ι h x }

variable (h : ∀ ι : Fin m' ↪ Fin n,
    U ≤ subframeMap (fullRelationSchemeEquivalence f hL d V c k) o a ι ⁻¹ᵁ U')
  (ι : Fin m' ↪ Fin n) (b₀ : Fin n)

/-- The actual exchange operator is linear over the unchanged original scalar ring. -/
def originalSubframeExchangeLinearMap :
    let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
    let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
    Tinv →ₗ[Ω] Γ(U.toScheme, ⊤) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k m' a W U' hU' hU'W
  let _ := normalizedOriginalRawAlgebra f hL d V c k n o W U hU hUW
  exact (originalSubframePullbackHom f hL d V c k n o W U hU hUW m' a U' hU' hU'W
    (ι.trans (Equiv.swap (ι a) b₀).toEmbedding) (h _)).toLinearMap -
  (originalSubframePullbackHom f hL d V c k n o W U hU hUW m' a U' hU' hU'W
    ι (h ι)).toLinearMap

omit [Etale V.hom] in
/-- Passing to original scalars retains exactly the original exchange error. -/
theorem originalSubframeExchangeLinearMap_apply (v : Tinv) :
    originalSubframeExchangeLinearMap f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ v =
        subframeExchangeMap e o a U U' hU' h ι b₀ v := rfl

end FLT.Mazur.HilbertChart.AffineRestriction
