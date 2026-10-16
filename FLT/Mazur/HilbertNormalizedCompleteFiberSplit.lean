/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedCompleteOrbits
public import FLT.Mazur.EquivalenceRelationCompleteFiberSplit
public import FLT.Mazur.EquivalenceRelationCompleteClosedLocus

/-!
# Split original Hilbert relation fibers at complete normalized lifts

Every original geometric Hilbert endpoint lifts to a complete normalized frame
with a stable affine orbit neighborhood and a split entire original relation
fiber. The splitting retains the original relation, not a selected subrelation.
Neighborhood exhaustiveness remains a separate source restriction problem.
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
variable (n : ℕ) (o : Fin n) {K : Type} [Field K]
  (u : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k n o)

/-- The entire original Hilbert relation fiber splits at every complete normalized frame. -/
def normalizedOriginalRelationFiberIso (hu : Complete (Fin n) o u) :
    (∐ fun _ : Equiv.Perm (Fin n) ↦ Spec (.of K)) ≅
      pullback (relationFirst p q (Fin n) o) u :=
  relationFiberSplitIso e (Fin n) o u hu

/-- The splitting retains the original Hilbert relation arrow on each permutation component. -/
@[reassoc] theorem normalizedOriginalRelationFiberIso_arrow
    (hu : Complete (Fin n) o u) (σ : Equiv.Perm (Fin n)) :
    Sigma.ι (fun _ : Equiv.Perm (Fin n) ↦ Spec (.of K)) σ ≫
      (normalizedOriginalRelationFiberIso f hL d V c k n o u hu).hom ≫
        pullback.fst (relationFirst p q (Fin n) o) u ≫ relationArrow p q (Fin n) o =
          u ≫ actionArrow («p» := p) («q» := q) (Fin n) o σ :=
  relationFiberSplitIso_arrow e (Fin n) o u hu σ

/-- Every point of a complete Hilbert orbit is intrinsically complete. -/
theorem normalizedCompleteOrbit_subset (hu : Complete (Fin n) o u) :
    frameOrbit e (Fin n) o (u default) ⊆
      completePointLocus («p» := p) («q» := q) (Fin n) o := by
  intro x hx
  obtain ⟨v, hv, hc⟩ := frameOrbit_complete_representative e (Fin n) o u hu x hx
  rw [← hv]
  exact (complete_iff_mem_completePointLocus (Fin n) o v).mp hc

/-- Every geometric endpoint has a complete stable affine lift with a split whole relation fiber. -/
theorem exists_normalized_complete_split_affine_lift [IsSepClosed K]
    (b : Spec (.of K) ⟶ A.left) :
    ∃ (m : ℕ) (j : Fin m)
      (v : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k m j)
      (U : (source p q (Fin m) j).Opens),
      v ≫ normalizedFullRelationFirst f hL d V c k m j = b ∧
      Complete (Fin m) j v ∧ IsAffineOpen U ∧ frameOrbit e (Fin m) j (v default) ⊆ U ∧
      (∀ σ : Equiv.Perm (Fin m),
        (normalizedFullRelationAction f hL d V c k m j σ).hom ⁻¹ᵁ U = U) ∧
      frameOrbit e (Fin m) j (v default) ⊆
        completePointLocus («p» := p) («q» := q) (Fin m) j ∧
      Nonempty ((∐ fun _ : Equiv.Perm (Fin m) ↦ Spec (.of K)) ≅
        pullback (relationFirst p q (Fin m) j) v) := by
  obtain ⟨m, j, v, U, hb, hv, hU, horbit, hstable⟩ :=
    exists_normalized_complete_affine_lift f hL d V c k b
  exact ⟨m, j, v, U, hb, hv, hU, horbit, hstable,
    normalizedCompleteOrbit_subset f hL d V c k m j v hv,
    ⟨normalizedOriginalRelationFiberIso f hL d V c k m j v hv⟩⟩

end FLT.Mazur.HilbertChart.AffineRestriction
