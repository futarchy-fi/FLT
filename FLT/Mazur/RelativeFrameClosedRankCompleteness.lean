/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameExactRank

/-!
# Complete original frames over closed rank bounds

A closed rank bound suffices for completeness at every coefficient field.
Unlike the original open rank bound, this statement reaches the lower-rank
residual points. It does not assert an open neighborhood in the original base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (n : ℕ)

/-- A closed original rank bound makes every n-frame complete over any field. -/
theorem geometric_complete_of_rankAtMost {K : Type} [Field K]
    {b : Spec (.of K) ⟶ S} (t : Over.mk b ⟶ distinctScheme E (Fin n))
    (hb : b default ∈ rankAtMost E n) :
    Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) t i default) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  apply (scalarFrame_complete_iff E (Fin n) t g).mp
  apply geometric_complete_of_no_larger E n (scalarFrame E (Fin n) t g)
  have hg : (g ≫ b) default = b default := congrArg b (Subsingleton.elim _ _)
  rw [hg]
  exact hb

/-- The full inverse image of a closed rank bound consists of complete original frames. -/
theorem rankAtMost_preimage_complete :
    (distinctScheme E (Fin n)).hom ⁻¹' rankAtMost E n ⊆ completeLocus E (Fin n) := by
  intro x hx
  let u := (distinctScheme E (Fin n)).left.fromSpecResidueField x
  let t : Over.mk (u ≫ (distinctScheme E (Fin n)).hom) ⟶ distinctScheme E (Fin n) :=
    Over.homMk u
  have hu : u default = x := Scheme.fromSpecResidueField_apply x default
  have hc := geometric_complete_of_rankAtMost E n t (by
    change (distinctScheme E (Fin n)).hom (u default) ∈ rankAtMost E n
    rwa [hu])
  have h := (geometric_complete_iff_mem_completeLocus E (Fin n) t).mp hc
  change u default ∈ completeLocus E (Fin n) at h
  rwa [hu] at h

/-- Every scheme-valued frame supported on the closed rank bound has complete image. -/
theorem frame_range_complete_of_rankAtMost {T : Scheme} {b : T ⟶ S}
    (t : Over.mk b ⟶ distinctScheme E (Fin n))
    (hb : Set.range b ⊆ rankAtMost E n) :
    Set.range t.left ⊆ completeLocus E (Fin n) := by
  rintro _ ⟨x, rfl⟩
  apply rankAtMost_preimage_complete E n
  have hw := congrArg (fun f ↦ f x) t.w
  change (t.left ≫ (distinctScheme E (Fin n)).hom) x ∈ rankAtMost E n
  rw [hw]
  exact hb (Set.mem_range_self x)

end FLT.Mazur.RelativeOrderedTuples
