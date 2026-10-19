/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceGeometricFiberTests
public import FLT.Mazur.EquivalenceRelationInvariantCharacterFibers

/-!
# Actual original arrows in every full invariant-character fiber

Every character of the full affine frame invariant ring over the canonical
residue closure has an original representative. All its lifts are joined by
unique original relation arrows. Completeness still has to be established at
one representative of each required invariant character; scalar equality alone
does not identify different invariant characters.
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
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)

local notation "τU" => restrictedAction τ U hU
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates τU σ
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] normalizedOriginalScalarMap
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  originalSourceCompatibleModule

attribute [local irreducible] OriginalPrimeIntegralFiber.localizedMap
  invariantSheaf sourceSheaf invariantInclusion originalClosedSectionPullback
  invariantScalarCoordinates

open SchemeScalarPrincipalNeighborhood

variable [IsAffine U.toScheme]
local instance invariantCharacterChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local instance invariantCharacterOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance invariantCharacterOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "rankOf" => boundaryPointRank n o U e hU σ κ

local instance invariantCharacterProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

open ScalarTestLocalization
attribute [local irreducible] boundaryPointRank boundaryScalarProjection

local notation "K" P => AlgebraicClosure (PrimeSpectrum.comap κ P).asIdeal.ResidueField
local notation "u" w => sourceCharacterMap (X := U.toScheme) w ≫ U.ι

/-- Full invariant characters have original representatives and unique arrows to all lifts. -/
theorem originalSource_invariant_character_orbit (P : PrimeSpectrum Tsource)
    (χ : Sinv →+* K P) (hχ : χ.comp σ = algebraMap Ω (K P)) :
    ∃ v : Γ(U.toScheme, ⊤) →+* K P,
      v.comp σ₀ = algebraMap Ω (K P) ∧ (∀ t : Sinv, v t.val = χ t) ∧
      ∀ w : Γ(U.toScheme, ⊤) →+* K P, (∀ t : Sinv, w t.val = χ t) →
        ∃! a : Spec (.of (K P)) ⟶ (relation f hL d V c k).left,
          a ≫ p = (u v) ≫ first p q (Fin n) o ∧
          a ≫ q = (u w) ≫ first p q (Fin n) o := by
  have hl : ∃ v : Γ(U.toScheme, ⊤) →+* K P, ∀ t : Sinv, v t.val = χ t :=
    exists_sourceCharacter_lift (G := Equiv.Perm (Fin n)) (X := U.toScheme)
      τU χ
  obtain ⟨v, hv⟩ := hl
  refine ⟨v, ?_, hv, ?_⟩
  · ext x
    unfold invariantScalarCoordinates
    change v ((σ x).val) = algebraMap Ω (K P) x
    exact (hv (σ x)).trans (congrArg (fun ψ : Ω →+* K P ↦ ψ x) hχ)
  · intro w hw
    exact invariant_character_original_arrow e (Fin n) o U hU v w
      (fun t ↦ (hv t).trans (hw t).symm)

/-- One complete lift per full invariant character suffices for the exact original fiber. -/
theorem originalSource_matching_of_complete_invariant_lifts (P : PrimeSpectrum Tsource)
    (hc : ∀ χ : Sinv →+* K P, χ.comp σ = algebraMap Ω (K P) →
      ∃ v : Γ(U.toScheme, ⊤) →+* K P,
        (∀ t : Sinv, v t.val = χ t) ∧ Complete (Fin n) o (u v)) :
    ∀ pointZ : boundaryProduct σ κ, boundaryScalarProjection σ κ pointZ = P →
      rankOf pointZ = n := by
  apply originalSource_matching_of_source_point_values f hL d V c k n o W U hU hUW P
  intro w hw
  let χ : Sinv →+* K P := w.comp
    { toFun := fun t ↦ t.val
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hχ : χ.comp σ = algebraMap Ω (K P) := by
    convert hw using 1
    unfold invariantScalarCoordinates
    rfl
  obtain ⟨v, hv, hvc⟩ := hc χ hχ
  have he : ∀ t : Sinv, v t.val = w t.val := hv
  exact complete_character_tests_vanish e (Fin n) o U hU w
    (complete_of_invariant_character e (Fin n) o U hU v w he hvc)

end FLT.Mazur.HilbertChart.AffineRestriction
