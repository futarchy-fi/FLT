/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryScalarRanks
public import FLT.Mazur.SchemeValuationImageClosure

/-!
# Higher original ranks witnessed at exact scalar valuation centers

A scalar prime is excluded precisely when a valuation square of the higher
rank open has that exact center. The witness can retain an actual minimal
component as its generic image. No Noetherian scalar product is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "π" => chartBoundaryProduct n o U e hU s κ
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local instance higherScalarValuationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance higherScalarValuationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance higherScalarValuationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
local notation "I" => boundaryTestIdeal s κ tests
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU s κ

/-- The higher-rank open mapped to the unchanged original scalar spectrum. -/
def boundaryHigherScalarMap :
    (boundaryRankOpen n o U e hU s κ (n + 1)).toScheme ⟶ Spec (.of T) :=
  (boundaryRankOpen n o U e hU s κ (n + 1)).ι ≫ boundaryScalarProjection s κ

local notation "higher" => boundaryRankOpen n o U e hU s κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU s κ

/-- Every excluded scalar prime admits a valuation with an original higher minimal component. -/
theorem boundaryHigherScalar_component_square (P : PrimeSpectrum T)
    (hP : P ∉ boundaryScalarNilpotenceOpen s κ tests) :
    ∃ (Q : minimalPrimes C) (S : ValuativeCommSq φ),
      (higher).ι (S.i₁ default) = boundaryComponentPoint s κ Q ∧
      S.i₂ (IsLocalRing.closedPoint S.R) = P := by
  obtain ⟨Q, hQ, hr⟩ :=
    (not_mem_boundaryScalarNilpotenceOpen_iff_higher n o U e hU s κ P).mp hP
  have hm : boundaryComponentPoint s κ Q ∈ higher :=
    (mem_boundaryRankOpen_iff n o U e hU s κ _ (n + 1)).mpr hr
  let x : (higher).toScheme := ⟨boundaryComponentPoint s κ Q, hm⟩
  have hx : φ x ⤳ P := (PrimeSpectrum.le_iff_specializes _ _).mp hQ
  obtain ⟨S, hS, hc⟩ := SchemeSpecializationValuation.exists_square φ x P hx
  exact ⟨Q, S, congrArg (fun y ↦ (higher).ι y) hS, hc⟩

/-- A valuation of the higher open at an exact scalar center certifies actual exclusion. -/
theorem boundaryHigherScalar_square_excludes (P : PrimeSpectrum T)
    (S : ValuativeCommSq φ) (hS : S.i₂ (IsLocalRing.closedPoint S.R) = P) :
    P ∉ boundaryScalarNilpotenceOpen s κ tests := by
  have hs := SchemeSpecializationValuation.square_specializes φ S
  rw [hS] at hs
  intro hp
  have hg := hs.mem_open (boundaryScalarNilpotenceOpen s κ tests).isOpen hp
  have hr := boundary_rank_matching_of_scalar_mem n o U e hU s κ
    ((higher).ι (S.i₁ default)) hg
  have hh := (mem_boundaryRankOpen_iff n o U e hU s κ _ (n + 1)).mp
    (S.i₁ default).property
  exact Nat.not_succ_le_self n (hh.trans hr.le)

/-- Exact-center valuation tests account for all generizing components, even with empty fibers. -/
theorem boundaryHigherScalar_square_iff (P : PrimeSpectrum T) :
    (∃ S : ValuativeCommSq φ, S.i₂ (IsLocalRing.closedPoint S.R) = P) ↔
      P ∉ boundaryScalarNilpotenceOpen s κ tests := by
  constructor
  · rintro ⟨S, hS⟩
    exact boundaryHigherScalar_square_excludes n o U e hU s κ P S hS
  · intro hP
    obtain ⟨_, S, _, hS⟩ := boundaryHigherScalar_component_square n o U e hU s κ P hP
    exact ⟨S, hS⟩

omit [TopologicalSpace.NoetherianSpace U.toScheme] in
/-- A matching exact fiber prevents any extension inside the higher-rank open. -/
theorem boundaryHigherScalar_no_lift (P : PrimeSpectrum T)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P → rankOf z = n)
    (S : ValuativeCommSq φ) (hS : S.i₂ (IsLocalRing.closedPoint S.R) = P) :
    ¬ S.commSq.HasLift := by
  intro hl
  obtain ⟨l⟩ := (CommSq.HasLift.iff S.commSq).mp hl
  have hc := (SchemeSpecializationValuation.lift_specializes φ S l).2.trans hS
  have hr := hf ((higher).ι (l.l (IsLocalRing.closedPoint S.R))) hc
  have hh := (mem_boundaryRankOpen_iff n o U e hU s κ _ (n + 1)).mp
    (l.l (IsLocalRing.closedPoint S.R)).property
  exact Nat.not_succ_le_self n (hh.trans hr.le)

/-- Matching fibers plus exact-center extension exclude every higher generizing component. -/
theorem boundaryScalar_mem_of_higher_lifts (P : PrimeSpectrum T)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P → rankOf z = n)
    (hl : ∀ S : ValuativeCommSq φ,
      S.i₂ (IsLocalRing.closedPoint S.R) = P → S.commSq.HasLift) :
    P ∈ boundaryScalarNilpotenceOpen s κ tests := by
  by_contra hp
  obtain ⟨S, hS⟩ := (boundaryHigherScalar_square_iff n o U e hU s κ P).mpr hp
  exact boundaryHigherScalar_no_lift n o U e hU s κ P hf S hS (hl S hS)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
