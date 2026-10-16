/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrderedAffineEnvelope
public import FLT.Mazur.HilbertNormalizedRelationComparison
public import FLT.Mazur.EquivalenceRelationNormalizedOrbitNeighborhood

/-!
# Affine neighborhoods for the moving normalized Hilbert action

The normalized source embeds openly in the original affine tuple envelope.
Finite orbits therefore have actual stable affine neighborhoods, also inside
any given open containing the orbit. Full-relation compatibility remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k

variable (n : ℕ) (o : Fin n)
local notation "N" => source p q (Fin n) o

/-- The normalized source embeds in the original affine tuple envelope. -/
def normalizedFrameEnvelopeMap : N ⟶
    (RelativeOrderedTuples.tuples (firstRelationEnvelope (A := A) V) (Fin n)).left :=
  inclusion p q (Fin n) o ≫ fullRelationOrderedEnvelopeMap f hL d V c k n

/-- This envelope retains the full scheme structure of the normalized source. -/
instance normalizedFrameEnvelopeMap_open :
    IsOpenImmersion (normalizedFrameEnvelopeMap f hL d V c k n o) := by
  let _ := inclusion_isOpenImmersion e (Fin n) o
  change IsOpenImmersion
    (inclusion p q (Fin n) o ≫ fullRelationOrderedEnvelopeMap f hL d V c k n)
  infer_instance

/-- Actual moving-endpoint orbits have stable affine neighborhoods inside prescribed opens. -/
theorem exists_normalizedFrame_stable_affine (x : N)
    (W : (source p q (Fin n) o).Opens)
    (hx : frameOrbit e (Fin n) o x ⊆ W) :
    ∃ U : (source p q (Fin n) o).Opens,
      IsAffineOpen U ∧ frameOrbit e (Fin n) o x ⊆ U ∧ U ≤ W ∧
      ∀ σ : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U := by
  let _ := RelativeOrderedTuples.finTuples_affine (firstRelationEnvelope (A := A) V) n
  exact exists_frameOrbit_affine_neighborhood e (Fin n) o
    (normalizedFrameEnvelopeMap f hL d V c k n o) x W hx

/-- Every normalized point is contained in a stable affine open for the moving action. -/
theorem exists_normalizedFrame_affine (x : N) :
    ∃ U : (source p q (Fin n) o).Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ σ : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U := by
  obtain ⟨U, hU, hxU, _, hstable⟩ :=
    exists_normalizedFrame_stable_affine f hL d V c k n o x ⊤ (by
      intro y hy
      trivial)
  exact ⟨U, hU, hxU (mem_frameOrbit e (Fin n) o x), hstable⟩

end FLT.Mazur.HilbertChart.AffineRestriction
