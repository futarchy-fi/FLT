/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeCoefficientScheme

/-!
# Comparison scheme base change for named coefficient equations

The tensor comparison applies to an arbitrary ring homomorphism and named
specialized equations. The resulting scheme isomorphism retains its base map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] comparisonCoefficientBaseChangeIso
variable {R A : Type} [CommRing R] [CommRing A]
  (W V : WeierstrassCurve R) (W' V' : WeierstrassCurve A) (f : R →+* A)
  (hW : W' = W.map f) (hV : V' = V.map f)
local notation "k" => Spec.map (CommRingCat.ofHom f)

/-- Named equations give the concrete coefficient pullback of the full comparison scheme. -/
def comparisonPresentationBaseChangeIso : comparisonScheme W' V' ≅
    pullback k (comparisonStructure W V) := by
  letI : Algebra R A := f.toAlgebra
  exact eqToIso (congrArg₂ comparisonScheme hW hV) ≪≫
    comparisonCoefficientBaseChangeIso (A := A) W V

/-- Transporting the equations leaves the refined coefficient-base projection unchanged. -/
@[reassoc] theorem comparisonPresentationBaseChangeIso_structure :
    (comparisonPresentationBaseChangeIso W V W' V' f hW hV).hom ≫ pullback.fst _ _ =
      comparisonStructure W' V' := by
  subst W'
  subst V'
  let _ : Algebra R A := f.toAlgebra
  exact comparisonCoefficientBaseChangeIso_structure (A := A) W V

end FLT.Mazur.WeierstrassChangeParameter
