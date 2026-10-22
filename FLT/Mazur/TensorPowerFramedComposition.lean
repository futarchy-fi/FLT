/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerFramePullback
public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Composition of framed tensor-power comparisons

Transporting an actual line and then evaluating in a frame agrees in every
degree with evaluating in the composite frame. Both pullback compositors
remain in the equality of sheaf morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor Scheme.Modules.pullback tensorIso
variable {X Y Z : Scheme}

/-- A frame evaluates a transported tensor power through the composite line frame. -/
theorem tensorPowerPullbackComparison_frame (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
    (e : (pullback f).obj L ≅ M) (v : M ≅ structureModule X) (n : ℕ) :
    (tensorPowerPullbackComparison f e n).hom ≫ (tensorPowerTrivialization v n).hom =
      (tensorPowerIso f L n).hom ≫ (tensorPowerTrivialization (e ≪≫ v) n).hom := by
  rw [tensorPowerPullbackComparison, Iso.trans_hom, Category.assoc,
    tensorPowerTrivialization_transport]

/-- Successive line transport and frame evaluation agree with the actual composite frame. -/
theorem tensorPowerFramedComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {L : Z.Modules} {M : Y.Modules} (e : (pullback g).obj L ≅ M)
    (v : (pullback f).obj M ≅ structureModule X) (n : ℕ) :
    (pullbackComp f g).inv.app (tensorPower L n) ≫
      (pullback f).map (tensorPowerPullbackComparison g e n).hom ≫
        (tensorPowerIso f M n).hom ≫ (tensorPowerTrivialization v n).hom =
      (tensorPowerIso (f ≫ g) L n).hom ≫
        (tensorPowerTrivialization
          ((pullbackComp f g).symm.app L ≪≫ (pullback f).mapIso e ≪≫ v) n).hom := by
  have hh := congrArg (fun a ↦ a.hom ≫
    (tensorPowerTrivialization (Iso.refl (structureModule X)) n).hom)
      (tensorPowerPullbackComparison_comp f g e v n)
  simpa only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, tensorPowerPullbackComparison_frame, Iso.trans_refl] using hh

end FLT.Mazur.FCurve
