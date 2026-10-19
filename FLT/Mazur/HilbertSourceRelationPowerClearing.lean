/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceResidualRankLifts
public import FLT.Mazur.SchemeQuasiCompactOpenKernelPower

/-!
# Original scalar powers clearing the full residual relation

A principal original scalar neighborhood inside the solved relation open
constructs compatible multiples of every raw boundary lift. Finite families
share one exponent. The relation itself need not be affine. Existence of an
avoiding original scalar is still a geometric input, not an assumed lift.
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
local notation "boundaryOrbitMap" => originalClosedInvariantMap f hL d V c k
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
local notation "Wc" => (TopologicalSpace.Opens.map (boundaryOrbitMap).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "E" => (pullOpen eo W).val

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
local notation "τU" => restrictedAction τ U hU
local notation "jU" => j ∣_ U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates τU σ
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] normalizedOriginalScalarMap
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

local notation "Bsource" => invariantCoordinates (boundaryOpenAction ρ τ j hj U hU)
local notation "α" => normalizedOriginalBoundaryHom f hL d V c k n o W U hU hUW


open RelativeOrderedTuples
attribute [local irreducible] originalSourceCompatibleModule
local notation "endpoint" => F ≫ kS
local notation "cutoff" => originalFrameRankCutoff f hL d V c k
local notation "good" => originalSourceGoodRelationOpen f hL d V c k n o U hU
local notation "Csource" => originalSourceCompatibleModule f hL d V c k n o W U hU hUW
local instance powerClearingOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance powerClearingOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
variable [IsAffine U.toScheme]


local notation "β" => normalizedBoundaryChartMap f hL d V c k n o U hU


local notation "Δ" => originalSourceRankDiscrepancy f hL d V c k n o U hU
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

/-- A finite family of raw numerators shares one actual original scalar power. -/
theorem originalSource_scalar_power_compatible_finite {I : Type} [Finite I]
    (x : Ω) (a : I → Sinv)
    (hx : (D).basicOpen ((F).appTop (σ x).val) ≤ good) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    ∃ power : ℕ, ∀ idx, σ (x ^ power) * a idx ∈ Csource := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := originalSource_doubleRelation_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)
  obtain ⟨power, hp⟩ := SchemeQuasiCompactOpenKernelPower.exists_pow_mul_eq_finite
    (good).ι ((F).appTop (σ x).val)
    (fun idx ↦ (F).appTop (a idx).val) (fun idx ↦ (H).appTop (a idx).val)
    (by simpa only [Scheme.Opens.opensRange_ι] using hx)
    (fun idx ↦ originalSourceGoodRelationOpen_equalizes f hL d V c k n o U hU (a idx))
  refine ⟨power, fun idx ↦ ?_⟩
  apply (mem_originalSourceCompatibleModule f hL d V c k n o W U hU hUW _).mpr
  change (F).appTop (σ (x ^ power) * a idx).val =
    (H).appTop (σ (x ^ power) * a idx).val
  simp only [map_pow, Subring.coe_mul, Subring.coe_pow, map_mul]
  rw [← normalizedOriginalScalarMap_full_source_relation f hL d V c k n o W U hU hUW x]
  exact hp idx

/-- One raw lift acquires full compatibility after an original scalar power. -/
theorem originalSource_scalar_power_compatible (x : Ω) (a : Sinv)
    (hx : (D).basicOpen ((F).appTop (σ x).val) ≤ good) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    ∃ power : ℕ, σ (x ^ power) * a ∈ Csource := by
  obtain ⟨power, hp⟩ := originalSource_scalar_power_compatible_finite
    f hL d V c k n o W U hU hUW x (fun _ : Unit ↦ a) hx
  exact ⟨power, hp ()⟩

/-- An avoiding original scalar produces every exact localized boundary lift. -/
theorem originalSource_surjective_of_relation_principal
    (P : Ideal Tsource) [P.IsPrime] (x : Ω) (hxP : κ x ∉ P)
    (hx : (D).basicOpen ((F).appTop (σ x).val) ≤ good) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  apply (originalSourceCompatible_surjective_iff_numerators
    f hL d V c k n o W U hU hUW P).mpr
  intro t
  obtain ⟨a, ha⟩ := normalizedBoundaryChartMap_surjective f hL d V c k n o U hU
    (show IsAffine U.toScheme from inferInstance) t
  obtain ⟨power, hp⟩ := originalSource_scalar_power_compatible
    f hL d V c k n o W U hU hUW x a hx
  refine ⟨x ^ power, ?_, σ (x ^ power) * a, ?_, ?_⟩
  · rw [map_pow]
    exact fun h ↦ hxP ((inferInstance : P.IsPrime).mem_of_pow_mem power h)
  · rw [map_mul, ha]
  · exact (mem_originalSourceCompatibleModule f hL d V c k n o W U hU hUW _).mp hp

end FLT.Mazur.HilbertChart.AffineRestriction
