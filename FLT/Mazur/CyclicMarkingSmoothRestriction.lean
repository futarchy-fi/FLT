/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularDivisor

/-!
# The full cyclic orbit divisor lies in the smooth group

The support argument includes repeated labels. It lifts the entire closed
subscheme, with its nilpotents, through the original smooth-open inclusion.
Restriction of the orbit ideal is exactly the product of group-section ideals.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- Every point of the orbit divisor lies in the given smooth group. -/
theorem cyclicMarkingIdeal_range_smooth :
    Set.range (E.cyclicMarkingIdeal φ).subschemeι ⊆ Set.range E.inclusion.left := by
  have : IsProper E.curve.hom := E.family.family.1
  rw [Scheme.IdealSheafData.range_subschemeι]
  intro x hx
  obtain ⟨i, _, hi⟩ := (FCurve.mem_support_prod Finset.univ
    (fun i : Fin n ↦ (φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion).left.ker) x).mp hx
  rw [← SetLike.mem_coe, FCurve.support_section_ker E.curve.hom
    (φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion).left (Over.w _)] at hi
  obtain ⟨z, rfl⟩ := hi
  exact ⟨(φ (.ofAdd (i.val : ZMod n))).left z, rfl⟩

/-- The whole orbit subscheme, including multiplicities, lifts to the smooth group. -/
def cyclicMarkingSmoothLift : (E.cyclicMarkingIdeal φ).subscheme ⟶ E.group.left :=
  IsOpenImmersion.lift E.inclusion.left (E.cyclicMarkingIdeal φ).subschemeι
    (E.cyclicMarkingIdeal_range_smooth φ)

/-- The lifted divisor retains its actual whole-curve closed immersion. -/
@[reassoc] theorem cyclicMarkingSmoothLift_inclusion :
    E.cyclicMarkingSmoothLift φ ≫ E.inclusion.left = (E.cyclicMarkingIdeal φ).subschemeι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The lift is a closed immersion into the original smooth group. -/
instance cyclicMarkingSmoothLift_closed : IsClosedImmersion (E.cyclicMarkingSmoothLift φ) := by
  have : IsClosedImmersion (E.cyclicMarkingSmoothLift φ ≫ E.inclusion.left) := by
    rw [cyclicMarkingSmoothLift_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp _ E.inclusion.left

/-- Restriction to the smooth group preserves every factor of the original orbit ideal. -/
theorem cyclicMarkingIdeal_restrict_smooth :
    (E.cyclicMarkingIdeal φ).comap E.inclusion.left =
      ∏ i : Fin n, (φ (.ofAdd (i.val : ZMod n))).left.ker := by
  have : IsProper E.curve.hom := E.family.family.1
  rw [cyclicMarkingIdeal, FCurve.idealSheaf_comap_prod]
  apply Finset.prod_congr rfl
  intro i _
  let s : S ⟶ E.group.left := (φ (.ofAdd (i.val : ZMod n))).left
  have : IsClosedImmersion (s ≫ E.inclusion.left) :=
    FCurve.isClosedImmersion_section E.curve.hom _
      (φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion).w
  have hp : IsPullback s (𝟙 S) E.inclusion.left (s ≫ E.inclusion.left) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  change (s ≫ E.inclusion.left).ker.comap E.inclusion.left = s.ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hp.isoPullback.hom, hp.isoPullback_hom_fst]

/-- The restricted whole-curve ideal is the exact ideal of the lifted orbit divisor. -/
theorem cyclicMarkingSmoothLift_ker :
    (E.cyclicMarkingSmoothLift φ).ker = (E.cyclicMarkingIdeal φ).comap E.inclusion.left := by
  have hp : IsPullback (E.cyclicMarkingSmoothLift φ) (𝟙 _) E.inclusion.left
      (E.cyclicMarkingIdeal φ).subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, cyclicMarkingSmoothLift_inclusion]⟩
  change _ = (pullback.fst E.inclusion.left (E.cyclicMarkingIdeal φ).subschemeι).ker
  rw [← Scheme.Hom.ker_comp_of_isIso hp.isoPullback.hom, hp.isoPullback_hom_fst]

end FLT.Mazur.GeneralizedEllipticCurve
