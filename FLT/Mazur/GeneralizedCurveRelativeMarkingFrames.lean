/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveRelativeMarkingSections
public import FLT.Mazur.FiniteProjectiveRankFrames
public import FLT.Mazur.ProperLineRankOneCohomology

/-!
# Exact pole frames on original singular generalized families

Every positive pole direct image has rank equal to its pole bound, and actual
frames with exactly that many sections. This uses the family's properness and
flatness, allowing arbitrary polygons, nilpotents, and mixed characteristic
on a noetherian affine base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve LineSectionBaseChange Chow
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group) (m : ℕ) (hm : 0 < m)

include hm

/-- The original pole section module has rank exactly m at every base point. -/
theorem smoothMarkingPower_section_rank (x : S) :
    Module.rankAtStalk (R := Γ(S, ⊤))
      (baseSections (E.smoothMarkingPower s m) E.curve.hom.appTop.hom ⊤)
      (S.isoSpec.hom x) = m := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Flat E.curve.hom := E.family.family.2.1
  let g := S.fromSpecResidueField x
  have h := properLineSectionRank_fieldFiber E.curve.hom _
    (E.smoothMarkingPower_rankOne s m) (E.smoothMarkingPower_residue_acyclic s m hm)
    (IsPullback.of_hasPullback E.curve.hom g) (IsLocalRing.closedPoint (S.residueField x))
  have hd := E.smoothMarkingPower_fieldFiber_h0 s m hm g
  have hx : g (IsLocalRing.closedPoint (S.residueField x)) = x :=
    S.fromSpecResidueField_apply x _
  exact (congrArg (fun y : S ↦ Module.rankAtStalk (R := Γ(S, ⊤))
    (baseSections (E.smoothMarkingPower s m) E.curve.hom.appTop.hom ⊤)
      (S.isoSpec.hom y)) hx).symm.trans (h.trans hd)

/-- Every original positive pole direct image has local frames with exactly m entries. -/
theorem smoothMarkingPower_frame (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty
      (((pushforward E.curve.hom).obj (E.smoothMarkingPower s m)).restrict U.ι ≅
        SheafOfModules.free (Fin m)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Flat E.curve.hom := E.family.family.2.1
  let L := E.smoothMarkingPower s m
  let _ := (E.smoothMarkingPower_rankOne s m).isFinitePresentation
  obtain ⟨hf, hp⟩ := E.smoothMarkingPower_sections_finite_projective s m hm
  let _ := hf
  let _ := hp
  let M := ModuleCat.of Γ(S, ⊤) (baseSections L E.curve.hom.appTop.hom ⊤)
  obtain ⟨U, hx, ⟨e⟩⟩ := finiteProjective_rank_pullback_frame M S.isoSpec.hom m x
    (E.smoothMarkingPower_section_rank s m hm x)
  exact ⟨U, hx, ⟨((restrictFunctor U.ι).mapIso
    (properPushforwardTildeIso E.curve.hom L)).symm ≪≫ e⟩⟩

/-- In particular the original identity has exact pole frames across all singular fibers. -/
theorem identityMarkingPower_frame (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ Nonempty
      (((pushforward E.curve.hom).obj
        (E.smoothMarkingPower (MonObj.one (X := E.group)) m)).restrict U.ι ≅
          SheafOfModules.free (Fin m)) :=
  E.smoothMarkingPower_frame (MonObj.one (X := E.group)) m hm x

end FLT.Mazur.GeneralizedEllipticCurve
