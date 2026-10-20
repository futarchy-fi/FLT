/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonTorus
public import FLT.Mazur.OneGonNodalCoefficientGroupProjection

/-!
# Torus coordinates on every zero-parameter arithmetic test

The actual smooth group of the original arithmetic degeneration becomes a
torus on any coefficient test killing the parameter, including nonreduced
tests. Its coordinate retains the entire original smooth-to-whole inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj

namespace FLT.Mazur.ArithmeticOneGonFiberTorus

open OneGonSmoothing WeierstrassIntegralChart WeierstrassDividedDepth

variable {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A]
  (t : R) (ht : algebraMap R A t = 0)

include ht in
/-- The zero-parameter test retains the exact original cubic equation. -/
theorem equation_zero :
    (equation t).map (algebraMap R A) = splitNodalEquation (-1 : Aˣ) := by
  rw [equation_map, ht]
  rfl

/-- The full tested smooth group is toric over the original coefficient test. -/
irreducible_def groupIso :
    relativeTestGroup t (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≅
      CommGrp.mk (MultiplicativeGroupScheme.gm A) :=
  (originalSmoothCoefficientGroupIso A (equation t)).symm ≪≫
    eqToIso (congrArg integralSmoothGroup (equation_zero A t ht)) ≪≫
      integralSmoothSplitNodalTorusIso (-1 : Aˣ)

/-- The corrected torus parametrization on the actual pullback smooth group. -/
def torusIso : MultiplicativeGroupScheme.gm A ≅
    (relativeTestGroup t (Spec.map (CommRingCat.ofHom (algebraMap R A)))).X :=
  (CommGrp.forget (Over (Spec (.of A)))).mapIso
    (ArithmeticOneGonTorus.inversion A ≪≫ (groupIso A t ht).symm)

instance torusIso_isMonHom : IsMonHom (torusIso A t ht).hom :=
  inferInstanceAs (IsMonHom
    (ArithmeticOneGonTorus.inversion A ≪≫ (groupIso A t ht).symm).hom.hom.hom.hom)

/-- The corrected parametrization retains its original two group factors. -/
theorem torusIso_hom :
    (torusIso A t ht).hom = ι[MultiplicativeGroupScheme.gm A] ≫
      (groupIso A t ht).inv.hom.hom.hom := rfl

/-- Its full-curve projection retains the original equation and coefficient transports. -/
@[reassoc] theorem torusIso_inclusion :
    (torusIso A t ht).hom.left ≫
      pullback.fst (relativeGroup t).X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫
          (relativeGroupInclusion t).left =
    ι[MultiplicativeGroupScheme.gm A].left ≫
      (splitNodalRelativeSmoothOverIso (-1 : Aˣ)).hom.left ≫
        (relativeGroupInclusion (0 : A)).left ≫
          eqToHom (congrArg integralCurve (equation_zero A t ht).symm) ≫
            integralCoefficientMorphism (S := A) (equation t) := by
  rw [torusIso_hom]
  simp only [Over.comp_left, Category.assoc]
  exact congrArg (ι[MultiplicativeGroupScheme.gm A].left ≫ ·)
    (nodalCoefficientGroupIso_inclusion_of_eq A (equation t) (-1 : Aˣ)
      (equation_zero A t ht) (groupIso A t ht) (groupIso_def A t ht))

end FLT.Mazur.ArithmeticOneGonFiberTorus
