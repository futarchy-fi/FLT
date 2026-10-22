/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionSquareTransportFrame

/-!
# Tensor frames through the original section square

The tensor frame constructed on the new marked line is the transport of
its original tensor frame. The structure-module tensor trivializations
are removed from the commuting power square explicitly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor Scheme.Modules.pullback
variable {P X T S : Scheme} (p : P ⟶ X) (t : T ⟶ P) (g : T ⟶ S) (s : S ⟶ X)
  (w : t ≫ p = g ≫ s) {L : X.Modules} {N : P.Modules}
  (e : (pullback p).obj L ≅ N) (a : (pullback s).obj L ≅ structureModule S)

/-- Evaluation of a power comparison in the structure frame is the original power frame. -/
theorem tensorPowerPullbackComparison_unitFrame {Y Z : Scheme} (f : Y ⟶ Z)
    {M : Z.Modules} (v : (pullback f).obj M ≅ structureModule Y) (n : ℕ) :
    (tensorPowerPullbackComparison f v n).hom ≫
      (tensorPowerTrivialization (Iso.refl (structureModule Y)) n).hom =
        (tensorPowerIso f M n).hom ≫ (tensorPowerTrivialization v n).hom := by
  simpa only [Iso.trans_refl] using
    tensorPowerPullbackComparison_frame f v (Iso.refl (structureModule Y)) n

/-- The tensor frame on the transported marked line retains the actual square comparison. -/
theorem sectionSquareTransportFrame_tensor (n : ℕ) :
    sectionSquareTransportIso p t g s w (tensorPowerPullbackComparison p e n) ≪≫
        tensorPowerIso t N n ≪≫
          tensorPowerTrivialization (sectionSquareTransportFrame p t g s w e a) n =
      pulledGlobalFrame g (tensorPowerIso s L n ≪≫ tensorPowerTrivialization a n) := by
  have hh := congrArg (fun v ↦ v.hom ≫
    (tensorPowerTrivialization (Iso.refl (structureModule T)) n).hom)
      (sectionSquareTransportFrame_power p t g s w e a n).eq
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, tensorPowerPullbackComparison_unitFrame] at hh
  have hu := tensorPowerTrivialization_pullback g (Iso.refl (structureModule S)) n
  simp only [pulledGlobalFrame, Functor.mapIso_refl, Iso.refl_trans,
    Iso.trans_hom, Functor.mapIso_hom] at hu
  rw [hu, ← Functor.map_comp_assoc, tensorPowerPullbackComparison_unitFrame] at hh
  apply Iso.ext
  simp only [sectionSquareTransportIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom, pulledGlobalFrame, Category.assoc]
  rw [hh]
  simp [pullbackCongr]

end FLT.Mazur.FCurve
