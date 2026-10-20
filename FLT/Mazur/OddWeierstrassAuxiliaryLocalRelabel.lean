/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFaithfulMarkingRelabel
public import FLT.Mazur.OddWeierstrassAuxiliaryLocalTorsion
public import FLT.Mazur.OddWeierstrassAuxiliaryRestrictedMarking

/-!
# Exact local auxiliary relabeling under arbitrary group-family comparisons

Every original group-family isomorphism matches the full auxiliary frames by
one label automorphism on an affine neighborhood of each base point. No
reducedness or characteristic-zero hypothesis on the base is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T : Scheme} (f g : T ⟶ levelThree.left)
  (e : auxiliarySchemeGroup f ≅ auxiliarySchemeGroup g)

/-- The actual family comparison matches all auxiliary labels locally on the original base. -/
theorem auxiliarySchemeMarking_local_relabel (x : T) :
    ∃ (r : MulAut (Labels 3)) (U : T.Opens), IsAffineOpen U ∧ x ∈ U ∧
      ∀ i, U.ι ≫ (auxiliarySchemeMarking f (r i)).left ≫ e.hom.hom.hom.hom.left =
        U.ι ≫ (auxiliarySchemeMarking g i).left := by
  let P := GroupMarkingTransport.transport _ _ e (auxiliarySchemeMarking f)
  have hP (i : Labels 3) : P i ^ 3 = 1 := by
    change (auxiliarySchemeMarking f i ≫ e.hom.hom.hom.hom) ^ 3 = 1
    rw [← pow_comp, auxiliarySchemeMarking_pow, one_comp]
  obtain ⟨a, U, hU, hxU, ha⟩ := auxiliarySchemeMarking_local_full g P hP x
  let _ : Nonempty U.toScheme := ⟨⟨x, hxU⟩⟩
  let m := auxiliaryRestrictedMarking g U.ι
  let v := GroupMarkingTransport.transport _ _ e (auxiliaryRestrictedMarking f U.ι)
  have hm : Function.Injective m := auxiliaryRestrictedMarking_injective g U.ι
  have hv : Function.Injective v :=
    (GroupMarkingTransport.transport_injective_iff _ _ e _).mpr
      (auxiliaryRestrictedMarking_injective f U.ι)
  have hav (i : Labels 3) : m (a i) = v i := by
    apply Over.OverMorphism.ext
    change U.ι ≫ (auxiliarySchemeMarking g (a i)).left =
      (U.ι ≫ (auxiliarySchemeMarking f i).left) ≫ e.hom.hom.hom.hom.left
    exact (ha i).symm.trans (Category.assoc _ _ _).symm
  obtain ⟨r, hr, _⟩ := FiniteFaithfulMarkingRelabel.existsUnique_relabel m v hm hv a hav
  refine ⟨r.symm, U, hU, hxU, fun i => ?_⟩
  have h := congrArg Over.Hom.left (hr (r.symm i))
  rw [r.apply_symm_apply] at h
  exact (Category.assoc _ _ _).symm.trans h.symm

end FLT.Mazur.OddWeierstrassParameter
