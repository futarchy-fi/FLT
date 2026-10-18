/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeComparisonScheme

/-!
# Reversing the actual full comparison parameter scheme

Inversion of the entire admissible change induces an actual isomorphism
between the two ordered comparison schemes. Reversing twice is the identity
on the full coordinate algebra, including nilpotent parameter directions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)

/-- Inversion of admissible changes commutes with every coefficient homomorphism. -/
theorem variableChange_map_inv {A B : Type} [CommRing A] [CommRing B]
    (C : VariableChange A) (f : A →+* B) : (C⁻¹).map f = (C.map f)⁻¹ :=
  map_inv (VariableChange.mapHom f) C

/-- The original full universal comparison supplies a reverse comparison parameter. -/
irreducible_def equationReverse : EquationRing V W →ₐ[R] EquationRing W V :=
  equationSpecialize V W (equationChange W V)⁻¹
    (by rw [← equationChange_equation W V, inv_smul_smul])

/-- The reverse parameter retains exactly the inverse of the original admissible change. -/
theorem equationReverse_change :
    (equationChange V W).map (equationReverse W V).toRingHom = (equationChange W V)⁻¹ := by
  rw [equationReverse_def]
  exact equationChange_specialize V W _ _

/-- Applying both parameter reversals fixes the complete universal change. -/
theorem equationReverse_twice :
    ((equationChange W V).map (equationReverse V W).toRingHom).map
      (equationReverse W V).toRingHom = equationChange W V :=
  (congrArg (fun C : VariableChange (EquationRing V W) ↦
      C.map (equationReverse W V).toRingHom) (equationReverse_change V W)).trans
    ((variableChange_map_inv (equationChange V W) (equationReverse W V).toRingHom).trans
      ((congrArg Inv.inv (equationReverse_change W V)).trans (inv_inv _)))

/-- Reversing twice fixes every function on the full comparison scheme. -/
theorem equationReverse_comp :
    (equationReverse W V).comp (equationReverse V W) = AlgHom.id R (EquationRing W V) := by
  apply equation_hom_ext W V
  exact (VariableChange.map_map (equationChange W V) (equationReverse V W).toRingHom
    (equationReverse W V).toRingHom).symm.trans
      ((equationReverse_twice W V).trans (VariableChange.map_id _).symm)

/-- The reverse parameters identify the two ordered comparison coordinate algebras. -/
def equationReverseEquiv : EquationRing W V ≃ₐ[R] EquationRing V W :=
  AlgEquiv.ofAlgHom (equationReverse V W) (equationReverse W V)
    (equationReverse_comp V W) (equationReverse_comp W V)

/-- Reversal is an actual scheme isomorphism between the ordered full comparison loci. -/
def comparisonReverseIso : comparisonScheme W V ≅ comparisonScheme V W :=
  Scheme.Spec.mapIso (equationReverseEquiv V W).toRingEquiv.toCommRingCatIso.op

/-- Reversal retains the original coefficient base. -/
@[reassoc] theorem comparisonReverseIso_structure :
    (comparisonReverseIso W V).hom ≫ comparisonStructure V W = comparisonStructure W V := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (equationReverse W V).comp_algebraMap

end FLT.Mazur.WeierstrassChangeParameter
