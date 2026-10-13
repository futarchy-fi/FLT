/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineSectionSquare
public import FLT.Mazur.TensorPowerPullbackComparison

/-!
# Tensor powers of commuting line squares

Coherence of the actual line comparisons propagates to every tensor power,
including degree zero, with the same scheme square and pullback transports.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor tensorIso
variable {X Y Z T : Scheme}

/-- Power comparisons preserve the composite of two actual line comparisons. -/
theorem tensorPowerPullbackComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : Z.Modules} {M : Y.Modules} {N : X.Modules}
    (e : (pullback g).obj L ≅ M) (v : (pullback f).obj M ≅ N) (d : ℕ) :
    (pullbackComp f g).symm.app (tensorPower L d) ≪≫
        (pullback f).mapIso (tensorPowerPullbackComparison g e d) ≪≫
          tensorPowerPullbackComparison f v d =
      tensorPowerPullbackComparison (f ≫ g)
        ((pullbackComp f g).symm.app L ≪≫ (pullback f).mapIso e ≪≫ v) d := by
  let w := (pullbackComp f g).symm.app L ≪≫ (pullback f).mapIso e ≪≫ v
  have he : (pullback f).map e.hom ≫ v.hom =
      (pullbackStageIso (f ≫ g) g f rfl L).hom ≫ w.hom := by
    simp [w, pullbackStageIso_hom, pullbackCongr]
  have ht := tensorPowerPullbackComparison_stage (f ≫ g) g f rfl e v w he d
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [ht]
  simp only [pullbackStageIso_hom, pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, Iso.inv_hom_id_app_assoc, w]

/-- Power comparisons preserve transport along an equality of scheme maps. -/
theorem tensorPowerPullbackComparison_congr {f g : X ⟶ Y} (hfg : f = g)
    {L : Y.Modules} {M : X.Modules} (e : (pullback g).obj L ≅ M) (d : ℕ) :
    tensorPowerPullbackComparison f ((pullbackCongr hfg).app L ≪≫ e) d =
      (pullbackCongr hfg).app (tensorPower L d) ≪≫ tensorPowerPullbackComparison g e d := by
  subst g
  have hi (A : Y.Modules) : (pullbackCongr (rfl : f = f)).app A = Iso.refl _ := by
    apply Iso.ext
    rfl
  rw [hi, Iso.refl_trans, hi, Iso.refl_trans]

/-- Every actual tensor power retains a commuting square of line comparisons. -/
theorem LinePullbackSquare.tensorPower
    {f : X ⟶ Y} {g : Y ⟶ T} {r : X ⟶ Z} {s : Z ⟶ T} {w : f ≫ g = r ≫ s}
    {A : T.Modules} {B : Y.Modules} {C : Z.Modules} {D : X.Modules}
    {eg : (pullback g).obj A ≅ B} {ef : (pullback f).obj B ≅ D}
    {es : (pullback s).obj A ≅ C} {er : (pullback r).obj C ≅ D}
    (he : LinePullbackSquare f g r s w eg ef es er) (d : ℕ) :
    LinePullbackSquare f g r s w
      (tensorPowerPullbackComparison g eg d) (tensorPowerPullbackComparison f ef d)
      (tensorPowerPullbackComparison s es d) (tensorPowerPullbackComparison r er d) := by
  unfold LinePullbackSquare
  rw [tensorPowerPullbackComparison_comp, he.eq,
    tensorPowerPullbackComparison_congr, tensorPowerPullbackComparison_comp]

end FLT.Mazur.FCurve
