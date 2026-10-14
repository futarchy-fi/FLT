/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FunctionSheafGradedSections
public import FLT.Mazur.SectionGradedStructuralAlgebra

/-!
# The section-ring comparison over the original structural base
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FunctionSheafGradedSections
open FCurve SectionGradedSum SectionGradedBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor

variable {X Y S : Scheme} (f : X ⟶ Y) [IsIso (StructureDirectImage.unitMap f)]
  {L : Y.Modules} {M : X.Modules} (hL : LocallyFreeRankOne L)
  (e : (pullback f).obj L ≅ M) (p : Y ⟶ S) (q : X ⟶ S) (w : f ≫ p = q)

include w in
/-- The ring comparison retains the original base coefficient homomorphism. -/
theorem ringEquiv_scalar (r : Γ(S, ⊤)) :
    ringEquiv f hL e (algebraMap Γ(S, ⊤) (sectionModule p L) r) =
      algebraMap Γ(S, ⊤) (sectionModule q M) r := by
  rw [structural_algebraMap, structural_algebraMap, ringEquiv_of,
    SectionGradedLinePullback.sectionMap_zero]
  have hw := congrArg (fun a : X ⟶ S ↦ a.appTop r) w
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hw
  exact congrArg (of M ⊤ 0) hw

/-- The original base actions make the full section-ring comparison an algebra isomorphism. -/
def algEquiv : sectionModule p L ≃ₐ[Γ(S, ⊤)] sectionModule q M :=
  { ringEquiv f hL e with
    commutes' := ringEquiv_scalar f hL e p q w }

/-- The algebra equivalence is the original ring equivalence on every section sum. -/
theorem algEquiv_apply (a : sectionModule p L) :
    algEquiv f hL e p q w a = ringEquiv f hL e a := rfl

end FLT.Mazur.FunctionSheafGradedSections
