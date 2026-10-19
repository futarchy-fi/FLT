/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedAffineNeighborhood
public import FLT.Mazur.EquivalenceRelationCompleteNeighborhoodCharacters

/-!
# Constructed complete Hilbert charts over an original integral generic endpoint

The full original Hilbert relation is finite near the original generic
parameter. A complete frame there acquires a stable affine neighborhood on
which all full invariant characters have complete original representatives.
The original parameter's generic point is not identified with an arbitrary
prime of the original scalar ring; that coverage remains a separate obligation.
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
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsIntegral A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

/-- The whole original Hilbert projection has a finite neighborhood at its generic parameter. -/
theorem originalProjection_generic_finite :
    genericPoint A.left ∈ finiteTargetOpen p := by
  let _ := QuasiCompactEtaleGeometricSections.locallyQuasiFinite p
  exact genericPoint_mem_finiteTarget p

/-- A fixed complete original generic frame gets a complete affine chart without changing n. -/
theorem exists_generic_normalized_character_chart (n : ℕ) (o : Fin n)
    (x : source p q (Fin n) o)
    (hx : first p q (Fin n) o x = genericPoint A.left)
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
  exact exists_generic_complete_character_chart e (Fin n) o
    (normalizedFrameEnvelopeMap f hL d V c k n o) x hx hc W hW

/-- Complete affine support is constructed from the original generic geometric parameter alone. -/
theorem exists_generic_complete_normalized_affine {K : Type} [Field K] [IsSepClosed K]
    (b : Spec (.of K) ⟶ A.left) (hb : b default = genericPoint A.left) :
    ∃ (n : ℕ) (o : Fin n) (u : Spec (.of K) ⟶ source p q (Fin n) o)
      (U : (source p q (Fin n) o).Opens),
      u ≫ first p q (Fin n) o = b ∧ Complete (Fin n) o u ∧
      IsAffineOpen U ∧ frameOrbit e (Fin n) o (u default) ⊆ U ∧
      (U : Set _) ⊆ completePointLocus («p» := p) («q» := q) (Fin n) o ∧
      ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U := by
  obtain ⟨n, o, u, hu, hc, hi⟩ := exists_generic_complete_interior_lift e b hb
  obtain ⟨U, hU, hO, hle, hs⟩ := exists_normalizedFrame_stable_affine
    f hL d V c k n o (u default) (completeInterior (Fin n) o)
    (frameOrbit_subset_completeInterior e (Fin n) o (u default) hi)
  exact ⟨n, o, u, U, hu, hc, hU, hO,
    fun z hz ↦ completeInterior_subset (Fin n) o (hle hz), hs⟩

end FLT.Mazur.HilbertChart.AffineRestriction
