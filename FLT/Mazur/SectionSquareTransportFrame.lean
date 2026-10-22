/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionSquareTransport
public import FLT.Mazur.TensorPowerFramedComposition

/-!
# The actual frame transported around a section square

The frame on the new marked line is constructed from the original frame
and the actual square comparison. Its line square commutes, and therefore
so do all of its tensor powers.
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

/-- The original marked-line frame transported through the actual square. -/
def sectionSquareTransportFrame : (pullback t).obj N ≅ structureModule T :=
  (sectionSquareTransportIso p t g s w e).symm ≪≫ pulledGlobalFrame g a

/-- The constructed frame satisfies the original commuting line square. -/
theorem sectionSquareTransportFrame_square :
    LinePullbackSquare t p g s w e (sectionSquareTransportFrame p t g s w e a)
      a (modulePullbackUnitIso g) := by
  unfold LinePullbackSquare sectionSquareTransportFrame sectionSquareTransportIso
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_inv, pulledGlobalFrame,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc]
  rfl

/-- Every actual tensor power retains the constructed marked-frame square. -/
theorem sectionSquareTransportFrame_power (n : ℕ) :
    LinePullbackSquare t p g s w
      (tensorPowerPullbackComparison p e n)
      (tensorPowerPullbackComparison t (sectionSquareTransportFrame p t g s w e a) n)
      (tensorPowerPullbackComparison s a n)
      (tensorPowerPullbackComparison g (modulePullbackUnitIso g) n) :=
  (sectionSquareTransportFrame_square p t g s w e a).tensorPower n

end FLT.Mazur.FCurve
