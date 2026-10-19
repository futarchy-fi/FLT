/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedAffineNeighborhood
public import FLT.Mazur.EquivalenceRelationMinimalCompleteNeighborhood
public import FLT.Mazur.EquivalenceRelationCompleteNeighborhoodCharacters

/-!
# Complete Hilbert charts over original minimal endpoints

Every minimal prime of the original Noetherian parameter ring has a finite
whole-relation neighborhood. Complete frames there acquire stable affine
charts with complete full invariant-character representatives. The original
parameter may be reducible or nonreduced; arbitrary scalar-domain coverage
is a separate problem.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsLocallyNoetherian A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

/-- The whole original Hilbert projection has a finite neighborhood at its minimal parameter. -/
theorem originalProjection_minimal_finite (a : A.left)
    (ha : (A.left.isoSpec.hom a).asIdeal ∈ minimalPrimes Γ(A.left, ⊤)) :
    a ∈ finiteTargetOpen p := by
  let _ := QuasiCompactEtaleGeometricSections.locallyQuasiFinite p
  exact affine_minimalPrime_mem_finiteTarget p a ha

/-- A fixed complete original minimal frame gets a complete affine chart without changing n. -/
theorem exists_minimal_normalized_character_chart (n : ℕ) (o : Fin n)
    (x : source p q (Fin n) o)
    (hx : (A.left.isoSpec.hom (first p q (Fin n) o x)).asIdeal ∈
      minimalPrimes Γ(A.left, ⊤))
    (hc : x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (W : (source p q (Fin n) o).Opens) (hW : frameOrbit e (Fin n) o x ⊆ W) :
    ∃ (U : (source p q (Fin n) o).Opens)
      (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
      (hA : IsAffineOpen U), frameOrbit e (Fin n) o x ⊆ U ∧ U ≤ W ∧
      let _ : IsAffine U.toScheme := hA
      ∀ (K : Type) [Field K] [IsAlgClosed K]
        (χ : invariantCoordinates (restrictedAction (action e (Fin n) o) U hU) →+* K),
        ∃ w : Γ(U.toScheme, ⊤) →+* K,
          (∀ t : invariantCoordinates (restrictedAction (action e (Fin n) o) U hU),
            w t.val = χ t) ∧ Complete (Fin n) o (sourceCharacterMap w ≫ U.ι) := by
  let _ := RelativeOrderedTuples.finTuples_affine (firstRelationEnvelope (A := A) V) n
  obtain ⟨U, hA, hO, hUW, hC, hU⟩ := exists_minimal_complete_affine e (Fin n) o
    (normalizedFrameEnvelopeMap f hL d V c k n o) x hx hc W hW
  refine ⟨U, hU, hA, hO, hUW, ?_⟩
  dsimp only
  intro K _ _ χ
  let _ : IsAffine U.toScheme := hA
  exact completeOpen_character_lift e (Fin n) o U hU hC χ

/-- Complete affine support is constructed from the original minimal geometric parameter alone. -/
theorem exists_minimal_complete_normalized_affine {K : Type} [Field K] [IsSepClosed K]
    (b : Spec (.of K) ⟶ A.left)
    (hb : (A.left.isoSpec.hom (b default)).asIdeal ∈ minimalPrimes Γ(A.left, ⊤)) :
    ∃ (n : ℕ) (o : Fin n) (u : Spec (.of K) ⟶ source p q (Fin n) o)
      (U : (source p q (Fin n) o).Opens),
      u ≫ first p q (Fin n) o = b ∧ Complete (Fin n) o u ∧
      IsAffineOpen U ∧ frameOrbit e (Fin n) o (u default) ⊆ U ∧
      (U : Set _) ⊆ completePointLocus («p» := p) («q» := q) (Fin n) o ∧
      ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U := by
  obtain ⟨n, o, u, hu, hc, hi⟩ := exists_minimal_complete_interior_lift e b hb
  obtain ⟨U, hU, hO, hle, hs⟩ := exists_normalizedFrame_stable_affine
    f hL d V c k n o (u default) (completeInterior (Fin n) o)
    (frameOrbit_subset_completeInterior e (Fin n) o (u default) hi)
  exact ⟨n, o, u, U, hu, hc, hU, hO,
    fun z hz ↦ completeInterior_subset (Fin n) o (hle hz), hs⟩

end FLT.Mazur.HilbertChart.AffineRestriction
