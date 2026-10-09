/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleLines
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exact attachment points of the middle conic and its two lines

The conic meets each horizontal line in the reduced base point u = 0,
with its ordered tangent slope. The two horizontal lines are disjoint when
the tangent coefficient is a unit.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
  (r : R) (hr : r * (r + W.a₁) = 0)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "T" => coord W 0 0 0 0 c 0
local notation "V" => coord W 0 0 0 0 c 1
local notation "U" => coord W 0 0 0 0 c 2

/-- The specified horizontal line attaches at its original origin. -/
def middleAttachment : A →ₐ[R] R :=
  (aeval (0 : R)).comp (middleLineMap W c h2 r hr)

/-- Attachment keeps the ordered tangent slope and sets t and u to zero. -/
@[simp] theorem middleAttachment_coord (i : Fin 3) :
    middleAttachment W c h2 r hr (coord W 0 0 0 0 c i) = ![0, r, 0] i := by
  fin_cases i <;> simp [middleAttachment]

/-- The same attachment is the actual conic point, with no coefficient discarded. -/
theorem middleAttachment_conic :
    (conicEvaluation W.a₁ c 0 r (by simpa using hr)).comp (middleConicMap W c h2) =
      middleAttachment W c h2 r hr := by
  apply hom_ext
  intro i
  fin_cases i <;> simp

/-- The attachment kernel is exactly the sum of the two component ideals. -/
theorem middleAttachment_ker : RingHom.ker (middleAttachment W c h2 r hr) =
    Ideal.span {U} ⊔ middleLineIdeal W c r := by
  let I : Ideal A := Ideal.span {U} ⊔ middleLineIdeal W c r
  let q := Ideal.Quotient.mkₐ R I
  have hu : q U = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span {U} ≤ I from le_sup_left) (Ideal.subset_span (Set.mem_singleton _)))
  have ht : q T = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show middleLineIdeal W c r ≤ I from le_sup_right) (Ideal.subset_span (Set.mem_insert _ _)))
  have hv : q V = q (algebraMap R A r) := by
    have h : q (V - algebraMap R A r) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show middleLineIdeal W c r ≤ I from le_sup_right)
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    simpa only [map_sub, AlgHom.commutes, sub_eq_zero] using h
  have he : (Algebra.ofId R (A ⧸ I)).comp (middleAttachment W c h2 r hr) = q := by
    refine hom_ext W 0 0 0 0 c (S := A ⧸ I) _ _ ?_
    intro i
    fin_cases i <;> simp [AlgHom.comp_apply, ht, hv, hu]
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz' : middleAttachment W c h2 r hr z = 0 := hz
    simpa only [AlgHom.comp_apply, hz', map_zero, q, I, Ideal.Quotient.mkₐ_eq_mk]
      using (DFunLike.congr_fun he z).symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact middleAttachment_coord W c h2 r hr 2
  · intro z hz
    have hz' : middleLineMap W c h2 r hr z = 0 := by
      change z ∈ RingHom.ker (middleLineMap W c h2 r hr)
      rwa [middleLineMap_ker]
    change aeval (0 : R) (middleLineMap W c h2 r hr z) = 0
    rw [hz', map_zero]

/-- The scheme-theoretic conic-line intersection is precisely the base. -/
def middleAttachmentQuotientEquiv :
    (A ⧸ (Ideal.span {U} ⊔ middleLineIdeal W c r)) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq R (middleAttachment_ker W c h2 r hr).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (fun z =>
      ⟨algebraMap R A z, (middleAttachment W c h2 r hr).commutes z⟩))

/-- The ordered horizontal lines have no intersection when their slopes are separated. -/
theorem middle_lines_disjoint (ha : IsUnit W.a₁) :
    middleLineIdeal W c 0 ⊔ middleLineIdeal W c (-W.a₁) = ⊤ := by
  let I := middleLineIdeal W c 0 ⊔ middleLineIdeal W c (-W.a₁)
  have hv : V ∈ I := by
    apply (show middleLineIdeal W c 0 ≤ I from le_sup_left)
    simp only [middleLineIdeal, map_zero, sub_zero]
    exact Ideal.subset_span (Set.mem_insert_of_mem T (Set.mem_singleton _))
  have hva : V + algebraMap R A W.a₁ ∈ I := by
    apply (show middleLineIdeal W c (-W.a₁) ≤ I from le_sup_right)
    simp only [middleLineIdeal, map_neg, sub_neg_eq_add]
    exact Ideal.subset_span (Set.mem_insert_of_mem T (Set.mem_singleton _))
  have haI : algebraMap R A W.a₁ ∈ I := by
    simpa only [add_sub_cancel_left] using I.sub_mem hva hv
  exact Ideal.eq_top_of_isUnit_mem I haI (ha.map (algebraMap R A))

end FLT.Mazur.WeierstrassSuccessiveX
