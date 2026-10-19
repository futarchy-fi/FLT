/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourcePrescribedInvariantLift
public import FLT.Mazur.EquivalenceRelationScalarFiberCorrections

/-!
# Full original Hilbert scalar-test corrections

Keep the original scalar map, boundary and n. A single ambient correction
solves all full infinitesimal scalar tests whose character geometry is
complete. This specializes the arbitrary infinitesimal scalar-test construction.
Character containment remains an independent geometric obligation.
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
  EquivalenceRelationNormalizedFrames.action restrictedAction
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
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ g : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
  [IsAffine U.toScheme]
local notation "α" => restrictedAction τ U hU
local notation "hj" => restrictedAction_hom_ι τ U hU
local notation "j" order => completeQuotientFrameInclusion e (Fin n) o U hU order
local notation "coeff" a:max order:max => completeQuotientCoefficient e (Fin n) o U hU a order
local notation "i" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "hi" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
local notation "β" => FiniteGroupEquivariantPullback.action α ρ τ U.ι i hj hi
local notation "b" => pullback.fst U.ι i
local notation "hb" => FiniteGroupEquivariantPullback.action_fst α ρ τ U.ι i hj hi
attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates α
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)
local notation "F" => SchemeRelationRestriction.fst p q
  (U.ι ≫ first p q (Fin n) o)
local notation "H" => SchemeRelationRestriction.snd p q
  (U.ι ≫ first p q (Fin n) o)
local notation "J" => completeAffineOrbitIdeal e (Fin n) o U hU
local notation "K" P:max => AlgebraicClosure (PrimeSpectrum.comap κ P).asIdeal.ResidueField
attribute [local irreducible] normalizedOriginalScalarMap invariantSheaf sourceSheaf
  invariantInclusion originalClosedSectionPullback
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

/-- Preserve a prescribed correction and solve every full infinitesimal original scalar test. -/
theorem originalSource_prescribed_full_scalar_test_correction
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val)
    (order : ℕ) (z : Γ(completeQuotientFrame e (Fin n) o U hU order, ⊤))
    (hz : (pullback.fst (j order) i).appTop z = 0)
    (he : (SourceRestriction.fst (j order) (j order)).appTop z -
        (SourceRestriction.snd (j order) (j order)).appTop z =
      (SourceRestriction.fst (j order) (j order)).appTop (coeff a order) -
        (SourceRestriction.snd (j order) (j order)).appTop (coeff a order)) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' order = z ∧
      ∀ P : PrimeSpectrum Tsource,
        (∀ χ : Sinv →+* K P, χ.comp σ = algebraMap Ω (K P) → J ≤ RingHom.ker χ) →
        ∀ (T : Scheme) (u : T ⟶ Spec (.of Ω)),
        (∀ x : T, u x = PrimeSpectrum.comap κ P) →
        let l := scalarTestRelationMap e (Fin n) o U hU σ u
        (l ≫ F).appTop z' - (l ≫ H).appTop z' =
          (l ≫ F).appTop a - (l ≫ H).appTop a := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  have hlift : ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' order = z ∧
      ∃ v' : Sinv, a - z' = v'.val :=
    originalSource_prescribed_invariant_correction f hL d V c k n o U hU
      t a ha order z hz he
  obtain ⟨z', hz', he', v', hv'⟩ := hlift
  refine ⟨z', hz', he', ?_⟩
  intro P hJ T u hu
  have h :
      (scalarTestRelationMap e (Fin n) o U hU σ u ≫ F).appTop v'.val =
      (scalarTestRelationMap e (Fin n) o U hU σ u ≫ H).appTop v'.val :=
    scalarTestRelation_equalizes e (Fin n) o U hU σ (PrimeSpectrum.comap κ P)
      (originalSource_invariantScalar_finiteType f hL d V c k n o W U hU hUW) hJ u hu v'
  rw [← hv', map_sub, map_sub] at h
  exact (sub_eq_sub_iff_sub_eq_sub.mp h).symm

end FLT.Mazur.HilbertChart.AffineRestriction
