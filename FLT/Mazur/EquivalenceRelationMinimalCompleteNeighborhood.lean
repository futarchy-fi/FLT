/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeMinimalPrimeFiniteTargetOpen
public import FLT.Mazur.EquivalenceRelationFiniteCompleteInterior

/-!
# Complete frame neighborhoods at original minimal endpoints

Whole-source finiteness near original minimal primes removes the complete
interior obstruction over affine Noetherian bases, retaining all components
and nilpotents. A fixed complete frame keeps its labels and original center.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] [IsLocallyNoetherian A]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- A complete frame over the original minimal endpoint lies in the actual complete interior. -/
theorem minimal_complete_mem_interior (x : source p q I o)
    (hx : (A.isoSpec.hom (first p q I o x)).asIdeal ∈ minimalPrimes Γ(A, ⊤))
    (hc : x ∈ completePointLocus (p := p) (q := q) I o) :
    x ∈ completeInterior (p := p) (q := q) I o := by
  apply complete_mem_interior_of_finiteTarget I o x hc
  let _ := QuasiCompactEtaleGeometricSections.locallyQuasiFinite p
  exact affine_minimalPrime_mem_finiteTarget p _ hx

/-- The same original labels acquire a complete stable affine neighborhood inside any orbit open. -/
theorem exists_minimal_complete_affine {Y : Scheme} [IsAffine Y]
    (j : source p q I o ⟶ Y) [IsOpenImmersion j]
    (x : source p q I o) (hx : (A.isoSpec.hom (first p q I o x)).asIdeal ∈ minimalPrimes Γ(A, ⊤))
    (hc : x ∈ completePointLocus (p := p) (q := q) I o)
    (W : (source p q I o).Opens) (hW : frameOrbit e I o x ⊆ W) :
    ∃ U : (source p q I o).Opens,
      IsAffineOpen U ∧ frameOrbit e I o x ⊆ U ∧ U ≤ W ∧
      (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o ∧
      ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ U = U := by
  have hi := frameOrbit_subset_completeInterior e I o x
    (minimal_complete_mem_interior I o x hx hc)
  obtain ⟨U, hU, hO, hle, hs⟩ := exists_frameOrbit_affine_neighborhood e I o j x
    (W ⊓ completeInterior I o) (fun z hz ↦ ⟨hW hz, hi hz⟩)
  exact ⟨U, hU, hO, hle.trans inf_le_left,
    fun z hz ↦ completeInterior_subset I o (hle hz).2, hs⟩

variable {K : Type} [Field K] [IsSepClosed K]

include e in
/-- Complete interior frames at the original minimal endpoint are constructed, not assumed. -/
theorem exists_minimal_complete_interior_lift (b : Spec (.of K) ⟶ A)
    (hb : (A.isoSpec.hom (b default)).asIdeal ∈ minimalPrimes Γ(A, ⊤)) :
    ∃ (n : ℕ) (o : Fin n) (u : Spec (.of K) ⟶ source p q (Fin n) o),
      u ≫ first p q (Fin n) o = b ∧ Complete (Fin n) o u ∧
      u default ∈ completeInterior (p := p) (q := q) (Fin n) o := by
  obtain ⟨n, o, u, hu, hc⟩ := exists_complete_normalized_lift e b
  refine ⟨n, o, u, hu, hc, minimal_complete_mem_interior (Fin n) o (u default) ?_ ?_⟩
  · change (A.isoSpec.hom ((u ≫ first p q (Fin n) o) default)).asIdeal ∈ _
    rwa [hu]
  · exact (complete_iff_mem_completePointLocus (Fin n) o u).mp hc

end FLT.Mazur.EquivalenceRelationNormalizedFrames
