/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeGenericFiniteTargetOpen
public import FLT.Mazur.EquivalenceRelationFiniteCompleteInterior

/-!
# Complete original frame neighborhoods at integral generic endpoints

Generic finiteness of the full original first projection removes the interior
obstruction at the original generic endpoint. A fixed complete frame keeps its
labels and receives a stable affine neighborhood of entirely complete points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsIntegral A]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- A complete frame over the original generic endpoint lies in the actual complete interior. -/
theorem generic_complete_mem_interior (x : source p q I o)
    (hx : first p q I o x = genericPoint A)
    (hc : x ∈ completePointLocus (p := p) (q := q) I o) :
    x ∈ completeInterior (p := p) (q := q) I o := by
  apply complete_mem_interior_of_finiteTarget I o x hc
  rw [hx]
  let _ := QuasiCompactEtaleGeometricSections.locallyQuasiFinite p
  exact genericPoint_mem_finiteTarget p

/-- The same original labels acquire a complete stable affine neighborhood inside any orbit open. -/
theorem exists_generic_complete_affine {Y : Scheme} [IsAffine Y]
    (j : source p q I o ⟶ Y) [IsOpenImmersion j]
    (x : source p q I o) (hx : first p q I o x = genericPoint A)
    (hc : x ∈ completePointLocus (p := p) (q := q) I o)
    (W : (source p q I o).Opens) (hW : frameOrbit e I o x ⊆ W) :
    ∃ U : (source p q I o).Opens,
      IsAffineOpen U ∧ frameOrbit e I o x ⊆ U ∧ U ≤ W ∧
      (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o ∧
      ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ U = U := by
  have hi := frameOrbit_subset_completeInterior e I o x
    (generic_complete_mem_interior I o x hx hc)
  obtain ⟨U, hU, hO, hle, hs⟩ := exists_frameOrbit_affine_neighborhood e I o j x
    (W ⊓ completeInterior I o) (fun z hz ↦ ⟨hW hz, hi hz⟩)
  exact ⟨U, hU, hO, hle.trans inf_le_left,
    fun z hz ↦ completeInterior_subset I o (hle hz).2, hs⟩

variable {K : Type} [Field K] [IsSepClosed K]

include e in
/-- Complete interior frames at the original generic endpoint are constructed, not assumed. -/
theorem exists_generic_complete_interior_lift (b : Spec (.of K) ⟶ A)
    (hb : b default = genericPoint A) :
    ∃ (n : ℕ) (o : Fin n) (u : Spec (.of K) ⟶ source p q (Fin n) o),
      u ≫ first p q (Fin n) o = b ∧ Complete (Fin n) o u ∧
      u default ∈ completeInterior (p := p) (q := q) (Fin n) o := by
  obtain ⟨n, o, u, hu, hc⟩ := exists_complete_normalized_lift e b
  refine ⟨n, o, u, hu, hc, generic_complete_mem_interior (Fin n) o (u default) ?_ ?_⟩
  · change (u ≫ first p q (Fin n) o) default = genericPoint A
    rw [hu, hb]
  · exact (complete_iff_mem_completePointLocus (Fin n) o u).mp hc

end FLT.Mazur.EquivalenceRelationNormalizedFrames
