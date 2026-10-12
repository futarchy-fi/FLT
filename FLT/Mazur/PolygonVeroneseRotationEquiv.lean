/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonRotationScalars
public import FLT.Mazur.PolygonVeroneseSectionRotation

/-!
# Graded automorphisms of the original compatible Veronese rings

The cyclic action laws hold in each original direct sum, even before choosing
an exact positive step. The inverse rotation reflects as well as preserves the
internal homogeneous degrees needed by projective spectrum functoriality.
-/

@[expose] public noncomputable section
open scoped DirectSum
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleSectionRotation compatibleVeroneseRotation

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) [NeZero n] (q : ℕ)

/-- Zero rotation fixes every original retained compatible section. -/
@[simp] theorem compatibleVeroneseRotation_zero :
    compatibleVeroneseRotation R n h q 0 = RingHom.id _ := by
  apply RingHom.ext
  intro s
  change compatibleVeroneseRotation R n h q 0 s = s
  induction s using DirectSum.induction_on with
  | zero => exact map_zero _
  | of d s =>
    rw [compatibleVeroneseRotation_of]
    congr 1
    apply Subtype.ext
    exact DFunLike.congr_fun (compatibleSectionRotation_zero R n h) s.val
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The original cyclic addition law acts on the entire retained section ring. -/
theorem compatibleVeroneseRotation_add (a b : ZMod n) :
    compatibleVeroneseRotation R n h q (a + b) =
      (compatibleVeroneseRotation R n h q a).comp (compatibleVeroneseRotation R n h q b) := by
  apply RingHom.ext
  intro s
  change compatibleVeroneseRotation R n h q (a + b) s =
    compatibleVeroneseRotation R n h q a (compatibleVeroneseRotation R n h q b s)
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [compatibleVeroneseRotation_of, compatibleVeroneseRotation_of,
      compatibleVeroneseRotation_of]
    congr 1
    apply Subtype.ext
    exact DFunLike.congr_fun (compatibleSectionRotation_add R n h a b) s.val
  | add s t hs ht => simp only [map_add, hs, ht]

/-- The inverse label supplies the inverse on the entire retained compatible algebra. -/
def compatibleVeroneseRotationEquiv (a : ZMod n) :
    CompatibleVeroneseSections R n h q ≃+* CompatibleVeroneseSections R n h q :=
  RingEquiv.ofRingHom (compatibleVeroneseRotation R n h q a)
    (compatibleVeroneseRotation R n h q (-a))
    (by rw [← compatibleVeroneseRotation_add, add_neg_cancel, compatibleVeroneseRotation_zero])
    (by rw [← compatibleVeroneseRotation_add, neg_add_cancel, compatibleVeroneseRotation_zero])

/-- The constructed rotation preserves and reflects the actual internal homogeneous degrees. -/
theorem compatibleVeroneseRotation_grade_iff (a : ZMod n) (d : ℕ)
    (s : CompatibleVeroneseSections R n h q) :
    compatibleVeroneseRotationEquiv R n h q a s ∈ compatibleVeroneseGrade R n h q d ↔
      s ∈ compatibleVeroneseGrade R n h q d := by
  constructor
  · intro hs
    have hh := compatibleVeroneseRotation_mem_grade R n h q (-a) d hs
    exact (compatibleVeroneseRotationEquiv R n h q a).symm_apply_apply s ▸ hh
  · exact compatibleVeroneseRotation_mem_grade R n h q a d

/-- Recomposition retains the cyclic action on the original compatible section carrier. -/
theorem compatibleVeroneseRotation_recompose (a : ZMod n)
    (s : CompatibleVeroneseSections R n h q) :
    compatibleVeroneseToSections R n h q (compatibleVeroneseRotation R n h q a s) =
      compatibleSectionRotation R n h a (compatibleVeroneseToSections R n h q s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [compatibleVeroneseRotation_of]
    change DirectSum.coeRingHom _ (DirectSum.of _ d _) =
      compatibleSectionRotation R n h a (DirectSum.coeRingHom _ (DirectSum.of _ d s))
    rw [DirectSum.coeRingHom_of, DirectSum.coeRingHom_of]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

variable [NeZero q]

/-- The original complete-base coefficients are fixed in every positive retained algebra. -/
theorem compatibleVeroneseRotation_algebraMap (a : ZMod n) (r : PowerSeries R) :
    compatibleVeroneseRotation R n h q a
        (algebraMap (PowerSeries R) (CompatibleVeroneseSections R n h q) r) =
      algebraMap (PowerSeries R) (CompatibleVeroneseSections R n h q) r := by
  apply compatibleVeroneseToSections_injective R n h q (NeZero.pos q)
  rw [compatibleVeroneseRotation_recompose]
  change compatibleSectionRotation R n h a
    (DirectSum.coeAlgHom (compatibleVeroneseDegree R n h q) (algebraMap (PowerSeries R) _ r)) =
      DirectSum.coeAlgHom (compatibleVeroneseDegree R n h q) (algebraMap (PowerSeries R) _ r)
  rw [AlgHom.commutes, compatibleSectionRotation_algebraMap]

end FLT.Mazur.PolygonInfinitesimalStages
