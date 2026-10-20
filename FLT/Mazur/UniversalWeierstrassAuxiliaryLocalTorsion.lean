/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSectionFamilyLocalFactorization
public import FLT.Mazur.UniversalWeierstrassAuxiliaryGeometricFull

/-!
# Actual local fullness of auxiliary torsion on arbitrary bases

Every finite family of four-torsion sections of the actual pulled-back group
agrees with original auxiliary labels on a common affine neighborhood of each
base point. This is equality of morphisms, not equality only on geometric tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T : Scheme} (f : T ⟶ levelFour.left)
  (P : 𝟙_ (Over T) ⟶ (auxiliarySchemeGroup f).X) (hP : P ^ 4 = 1)

/-- The actual torsion section determines a point of the original auxiliary torsion scheme. -/
def auxiliarySchemeTorsionParameter : T ⟶ auxiliaryFourTorsion := by
  let e := GroupMarkingBaseChange.pointsMulEquiv (f ≫ levelFour.hom)
    universalGroup (𝟙_ (Over T))
  let p := e.symm P
  have hp : p ^ 4 = 1 := by
    change (e.symm P) ^ 4 = 1
    rw [← map_pow, hP, map_one]
  let t := GroupTorsionScheme.lift universalGroup 4 p hp
  exact pullback.lift t.left f (t.w.trans (Category.id_comp _))

/-- The torsion parameter retains the original auxiliary level point. -/
@[reassoc] theorem auxiliarySchemeTorsionParameter_map :
    auxiliarySchemeTorsionParameter f P hP ≫ auxiliaryFourTorsionMap = f :=
  pullback.lift_snd _ _ _

/-- Projection recovers the original section in the actual universal group. -/
@[reassoc] theorem auxiliarySchemeTorsionParameter_inclusion :
    auxiliarySchemeTorsionParameter f P hP ≫
      pullback.fst fourTorsion.hom levelFour.hom ≫
        (GroupTorsionScheme.inclusion universalGroup 4).left =
      P.left ≫ pullback.fst universalGroup.hom (f ≫ levelFour.hom) := by
  let e := GroupMarkingBaseChange.pointsMulEquiv (f ≫ levelFour.hom)
    universalGroup (𝟙_ (Over T))
  have h := GroupMarkingBaseChange.pointsMulEquiv_fst (f ≫ levelFour.hom)
    universalGroup (𝟙_ (Over T)) (e.symm P)
  change (e (e.symm P)).left ≫ _ = _ at h
  rw [e.apply_symm_apply] at h
  rw [auxiliarySchemeTorsionParameter, pullback.lift_fst_assoc]
  exact (congrArg Over.Hom.left (GroupTorsionScheme.lift_inclusion _ _ _ _)).trans h.symm

/-- Finitely many actual torsion sections have simultaneous original labels locally. -/
theorem auxiliarySchemeMarking_local_full {J : Type*} [Finite J]
    (Q : J → (𝟙_ (Over T) ⟶ (auxiliarySchemeGroup f).X))
    (hQ : ∀ j, Q j ^ 4 = 1) (x : T) :
    ∃ (a : J → Labels 4) (U : T.Opens), IsAffineOpen U ∧ x ∈ U ∧
      ∀ j, U.ι ≫ (Q j).left = U.ι ≫ (auxiliarySchemeMarking f (a j)).left := by
  obtain ⟨a, U, hU, hxU, he⟩ := OpenSectionFamilyLocalFactorization.exists_affine_family
    auxiliaryFourTorsionMap auxiliaryTorsionSection auxiliaryTorsionSection_map
    auxiliaryTorsionSection_covers (fun j => auxiliarySchemeTorsionParameter f (Q j) (hQ j))
    f (fun j => auxiliarySchemeTorsionParameter_map f (Q j) (hQ j)) x
  refine ⟨a, U, hU, hxU, fun j => ?_⟩
  apply pullback.hom_ext
  · change (U.ι ≫ (Q j).left) ≫
        pullback.fst universalGroup.hom (f ≫ levelFour.hom) =
      (U.ι ≫ (auxiliarySchemeMarking f (a j)).left) ≫
        pullback.fst universalGroup.hom (f ≫ levelFour.hom)
    have h := congrArg (fun z => z ≫ pullback.fst fourTorsion.hom levelFour.hom ≫
        (GroupTorsionScheme.inclusion universalGroup 4).left) (he j)
    simpa only [Category.assoc, auxiliarySchemeTorsionParameter_inclusion,
      auxiliaryTorsionSection_fst_assoc, ← Over.comp_left, auxiliaryTorsionMarking_inclusion,
      auxiliarySchemeMarking_fst] using h
  · have h₁ := (Q j).w
    have h₂ := (auxiliarySchemeMarking f (a j)).w
    exact (Category.assoc _ _ _).trans ((congrArg (U.ι ≫ ·) (h₁.trans h₂.symm)).trans
      (Category.assoc _ _ _).symm)

end FLT.Mazur.UniversalWeierstrass
