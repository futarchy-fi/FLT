/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedFrameRelation
public import FLT.Mazur.EquivalenceRelationCompletePointLocus

/-!
# Complete mixed frames have the same size

The full original arrow transports one complete frame to the other's entire
fiber. Their finite index types are therefore equivalent. In particular the
whole mixed relation has no point with two complete endpoints of unequal size.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  (I J : Type) [Fintype I] [Fintype J] (o : I) (o' : J)
  {K : Type} [Field K] (u : Spec (.of K) ⟶ source p q I o)
  (v : Spec (.of K) ⟶ source p q J o')
  (hu : Complete I o u) (hv : Complete J o' v)
  (a : Spec (.of K) ⟶ D) (ha : a ≫ p = u ≫ first p q I o)
  (hb : a ≫ q = v ≫ first p q J o')

local instance mixedCardOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

/-- Independent complete label types enumerate the same entire transported original fiber. -/
def completeIndexEquiv : I ≃ J :=
  (Equiv.ofBijective _ (comparisonFrame_complete e I o u hu a ha)).trans
    (Equiv.ofBijective _ (targetFrame_complete J o' v hv a hb)).symm

include e o o' u v hu hv a ha hb in
/-- Every original arrow between complete frames forces equal finite cardinalities. -/
theorem complete_cardinality : Fintype.card I = Fintype.card J :=
  Fintype.card_congr (completeIndexEquiv e I J o o' u v hu hv a ha hb)

include e in
/-- Independently chosen finite sizes coincide whenever both original endpoints are complete. -/
theorem complete_sizes_eq {n m : ℕ} (o : Fin n) (o' : Fin m)
    (z : Spec (.of K) ⟶ relation p q (Fin n) (Fin m) o o')
    (h₁ : Complete (Fin n) o (z ≫ fst p q (Fin n) (Fin m) o o'))
    (h₂ : Complete (Fin m) o' (z ≫ snd p q (Fin n) (Fin m) o o')) : n = m := by
  have h := complete_cardinality e (Fin n) (Fin m) o o'
    (z ≫ fst p q (Fin n) (Fin m) o o') (z ≫ snd p q (Fin n) (Fin m) o o') h₁ h₂
    (z ≫ arrow p q (Fin n) (Fin m) o o')
    (by simp only [Category.assoc, arrow_first])
    (by simp only [Category.assoc, arrow_second])
  simpa only [Fintype.card_fin] using h

variable [Etale p]

include e in
/-- Unequal-size complete source loci have no arrow in the entire original mixed relation. -/
theorem unequal_complete_loci_disjoint {n m : ℕ} (o : Fin n) (o' : Fin m) (hnm : n ≠ m) :
    Disjoint
      (fst p q (Fin n) (Fin m) o o' ⁻¹' completePointLocus (p := p) (q := q) (Fin n) o)
      (snd p q (Fin n) (Fin m) o o' ⁻¹' completePointLocus (p := p) (q := q) (Fin m) o') := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  let z := (relation p q (Fin n) (Fin m) o o').fromSpecResidueField x
  have hz : z default = x := Scheme.fromSpecResidueField_apply x default
  apply hnm
  apply complete_sizes_eq e o o' z
  · rw [complete_iff_mem_completePointLocus]
    change fst p q (Fin n) (Fin m) o o' (z default) ∈ _
    rwa [hz]
  · rw [complete_iff_mem_completePointLocus]
    change snd p q (Fin n) (Fin m) o o' (z default) ∈ _
    rwa [hz]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
