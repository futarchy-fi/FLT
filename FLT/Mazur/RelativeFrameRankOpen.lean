/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameRankBound
public import FLT.Mazur.RelativeGeometricFrameLocus
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Original open domains with bounded frame size

Remove the closure of the actual image of (n+1)-frames. Over the resulting
original base open every n-frame is complete, over arbitrary residue fields.
No assertion that these opens cover every base point is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (n : ℕ)

/-- The original base open excluding the closure of the larger-frame image. -/
def rankBoundOpen : S.Opens :=
  ⟨(closure (Set.range (distinctScheme E (Fin (n + 1))).hom))ᶜ,
    isClosed_closure.isOpen_compl⟩

omit [Etale E.hom] [QuasiCompact E.hom] in
/-- Points of the constructed open support no larger original frame. -/
theorem rankBoundOpen_no_larger {x : S} (hx : x ∈ rankBoundOpen E n) :
    x ∉ Set.range (distinctScheme E (Fin (n + 1))).hom :=
  fun h ↦ hx (subset_closure h)

/-- Original rank exclusion forces complete n-frames over arbitrary coefficient fields. -/
theorem geometric_complete_of_rankBound {K : Type} [Field K]
    {b : Spec (.of K) ⟶ S} (t : Over.mk b ⟶ distinctScheme E (Fin n))
    (hb : b default ∈ rankBoundOpen E n) :
    Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) t i default) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  apply (scalarFrame_complete_iff E (Fin n) t g).mp
  apply geometric_complete_of_no_larger E n (scalarFrame E (Fin n) t g)
  have hg : (g ≫ b) default = b default := congrArg b (Subsingleton.elim _ _)
  rw [hg]
  exact rankBoundOpen_no_larger E n hb

/-- All original tuple points above the constructed open lie in the complete locus. -/
theorem rankBound_preimage_complete :
    (distinctScheme E (Fin n)).hom ⁻¹' (rankBoundOpen E n : Set S) ⊆
      completeLocus E (Fin n) := by
  intro x hx
  let u := (distinctScheme E (Fin n)).left.fromSpecResidueField x
  let t : Over.mk (u ≫ (distinctScheme E (Fin n)).hom) ⟶ distinctScheme E (Fin n) :=
    Over.homMk u
  have hu : u default = x := Scheme.fromSpecResidueField_apply x default
  have hc := geometric_complete_of_rankBound E n t (by
    change (distinctScheme E (Fin n)).hom (u default) ∈ rankBoundOpen E n
    rwa [hu])
  have h := (geometric_complete_iff_mem_completeLocus E (Fin n) t).mp hc
  change u default ∈ completeLocus E (Fin n) at h
  rwa [hu] at h

/-- The constructed preimage is inside the interior, not merely the closed complete locus. -/
theorem rankBound_preimage_interior :
    (distinctScheme E (Fin n)).hom ⁻¹' (rankBoundOpen E n : Set S) ⊆
      interior (completeLocus E (Fin n)) :=
  interior_maximal (rankBound_preimage_complete E n)
    ((rankBoundOpen E n).isOpen.preimage (distinctScheme E (Fin n)).hom.continuous)

end FLT.Mazur.RelativeOrderedTuples
