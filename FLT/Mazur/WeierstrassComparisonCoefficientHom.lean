/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeEquationUniversal

/-!
# Actual coefficient morphisms of full comparison algebras

The morphism retains the universal admissible change and the prescribed
coefficient map. These two properties determine it uniquely.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A]
  (W V : WeierstrassCurve R) (W' V' : WeierstrassCurve A) (f : R →+* A)
  (hW : W' = W.map f) (hV : V' = V.map f)
local notation "Q" => EquationRing W V
local notation "Q'" => EquationRing W' V'

include hW hV in
/-- The original equations hold for the universal change on the named refined equations. -/
theorem comparisonPresentation_equation :
    equationChange W' V' • V.map ((algebraMap A Q').comp f) =
      W.map ((algebraMap A Q').comp f) := by
  rw [← WeierstrassCurve.map_map, ← WeierstrassCurve.map_map, ← hW, ← hV]
  exact equationChange_equation W' V'

/-- The coefficient morphism of full comparison algebras for arbitrary named equations. -/
def comparisonPresentationHom : Q →+* Q' := by
  letI : Algebra R A := f.toAlgebra
  exact (equationSpecialize W V (equationChange W' V')
    (comparisonPresentation_equation W V W' V' f hW hV)).toRingHom

/-- The coefficient morphism retains exactly the specified original coefficient map. -/
theorem comparisonPresentationHom_base :
    (comparisonPresentationHom W V W' V' f hW hV).comp (algebraMap R Q) =
      (algebraMap A Q').comp f := by
  let _ : Algebra R A := f.toAlgebra
  exact (equationSpecialize W V (equationChange W' V')
    (comparisonPresentation_equation W V W' V' f hW hV)).comp_algebraMap

/-- The coefficient morphism retains the entire universal admissible change. -/
theorem comparisonPresentationHom_change :
    (equationChange W V).map (comparisonPresentationHom W V W' V' f hW hV) =
      equationChange W' V' := by
  let _ : Algebra R A := f.toAlgebra
  exact equationChange_specialize W V (equationChange W' V')
    (comparisonPresentation_equation W V W' V' f hW hV)

/-- The base map and the full admissible change determine a comparison algebra morphism. -/
theorem comparisonPresentationHom_ext (a d : Q →+* Q')
    (ha : a.comp (algebraMap R Q) = (algebraMap A Q').comp f)
    (hd : d.comp (algebraMap R Q) = (algebraMap A Q').comp f)
    (hc : (equationChange W V).map a = (equationChange W V).map d) : a = d := by
  let _ : Algebra R A := f.toAlgebra
  let a' : Q →ₐ[R] Q' := ⟨a, DFunLike.congr_fun ha⟩
  let d' : Q →ₐ[R] Q' := ⟨d, DFunLike.congr_fun hd⟩
  exact congrArg AlgHom.toRingHom (equation_hom_ext W V a' d' hc)

end FLT.Mazur.WeierstrassChangeParameter
