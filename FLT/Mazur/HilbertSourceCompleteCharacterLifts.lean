/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceInvariantCharacterOrbits
public import FLT.Mazur.EquivalenceRelationCompleteCharacterLifts

/-!
# Complete lifts at the original scalar residue closure

The original orbit ideal gives an exact obstruction for the already constructed
character orbit to be complete. Its vanishing constructs complete original
representatives, and the original scalar triangle and every relation arrow
are preserved. Vanishing at all required scalar characters remains to prove.
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
local instance completeCharacterChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local instance completeCharacterOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance completeCharacterOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "rankOf" => boundaryPointRank n o U e hU σ κ

local instance completeCharacterProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

open ScalarTestLocalization
attribute [local irreducible] boundaryPointRank boundaryScalarProjection

local notation "K" P => AlgebraicClosure (PrimeSpectrum.comap κ P).asIdeal.ResidueField
local notation "u" w => sourceCharacterMap (X := U.toScheme) w ≫ U.ι

local notation "J" => completeAffineOrbitIdeal e (Fin n) o U hU

/-- The actual complete-orbit ideal exactly detects a complete lift of a full character. -/
theorem originalSource_complete_character_lift_iff (P : PrimeSpectrum Tsource)
    (χ : Sinv →+* K P) :
    (∃ v : Γ(U.toScheme, ⊤) →+* K P,
      (∀ t : Sinv, v t.val = χ t) ∧ Complete (Fin n) o (u v)) ↔
      J ≤ RingHom.ker χ := by
  constructor
  · rintro ⟨v, hv, hc⟩ t ht
    have hz := (complete_character_iff_orbit_ideal e (Fin n) o U hU v).mp hc t ht
    exact (hv t).symm.trans hz
  · exact exists_complete_character_lift e (Fin n) o U hU χ

/-- The W444 original orbit becomes complete when its independently defined ideal vanishes. -/
theorem originalSource_complete_character_orbit (P : PrimeSpectrum Tsource)
    (χ : Sinv →+* K P) (hχ : χ.comp σ = algebraMap Ω (K P))
    (hJ : J ≤ RingHom.ker χ) :
    ∃ v : Γ(U.toScheme, ⊤) →+* K P,
      v.comp σ₀ = algebraMap Ω (K P) ∧ (∀ t : Sinv, v t.val = χ t) ∧
      Complete (Fin n) o (u v) ∧
      ∀ w : Γ(U.toScheme, ⊤) →+* K P, (∀ t : Sinv, w t.val = χ t) →
        Complete (Fin n) o (u w) ∧
          ∃! a : Spec (.of (K P)) ⟶ (relation f hL d V c k).left,
            a ≫ p = (u v) ≫ first p q (Fin n) o ∧
            a ≫ q = (u w) ≫ first p q (Fin n) o := by
  have horbit : ∃ v : Γ(U.toScheme, ⊤) →+* K P,
      v.comp σ₀ = algebraMap Ω (K P) ∧ (∀ t : Sinv, v t.val = χ t) ∧
      ∀ w : Γ(U.toScheme, ⊤) →+* K P, (∀ t : Sinv, w t.val = χ t) →
        ∃! a : Spec (.of (K P)) ⟶ (relation f hL d V c k).left,
          a ≫ p = (u v) ≫ first p q (Fin n) o ∧
          a ≫ q = (u w) ≫ first p q (Fin n) o :=
    originalSource_invariant_character_orbit f hL d V c k n o W U hU hUW P χ hχ
  obtain ⟨v, hvσ, hv, harrow⟩ := horbit
  have hc : Complete (Fin n) o (u v) := by
    apply (complete_character_iff_orbit_ideal e (Fin n) o U hU v).mpr
    exact fun t ht ↦ (hv t).trans (hJ ht)
  refine ⟨v, hvσ, hv, hc, fun w hw ↦ ⟨?_, harrow w hw⟩⟩
  exact complete_of_invariant_character e (Fin n) o U hU v w
    (fun t ↦ (hv t).trans (hw t).symm) hc

/-- Ideal vanishing for every required full character supplies the original matching fiber. -/
theorem originalSource_matching_of_character_ideal (P : PrimeSpectrum Tsource)
    (hJ : ∀ χ : Sinv →+* K P, χ.comp σ = algebraMap Ω (K P) →
      J ≤ RingHom.ker χ) :
    ∀ pointZ : boundaryProduct σ κ, boundaryScalarProjection σ κ pointZ = P →
      rankOf pointZ = n := by
  apply originalSource_matching_of_complete_invariant_lifts f hL d V c k n o W U hU hUW P
  intro χ hχ
  exact (originalSource_complete_character_lift_iff f hL d V c k n o W U hU P χ).mpr
    (hJ χ hχ)

end FLT.Mazur.HilbertChart.AffineRestriction
