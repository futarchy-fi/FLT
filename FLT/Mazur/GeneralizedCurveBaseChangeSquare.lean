/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedComparisonPullbackNaturality

/-!
# Full curve base change along a commuting square

The two iterated pullbacks along a named commuting square are naturally
isomorphic, including all generalized-curve structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (s : T ⟶ S) (k : U ⟶ S) (t : V ⟶ U) (p : V ⟶ T)
  (h : t ≫ k = p ≫ s)

/-- The full base-change functors on the two paths of a square agree naturally. -/
def baseChangeSquare : baseChangeFunctor k ⋙ baseChangeFunctor t ≅
    baseChangeFunctor s ⋙ baseChangeFunctor p :=
  (baseChangeComp k t).symm ≪≫ baseChangeCongr h ≪≫ baseChangeComp s p

/-- The square comparison is the direct-to-iterated comparison on both paths. -/
theorem baseChangeSquare_app (E : GeneralizedEllipticCurve S) :
    (baseChangeSquare s k t p h).app E =
      (E.baseChangeCompIso k t).symm ≪≫ E.baseChangeCompEqIso s p (t ≫ k) h := rfl

/-- The square retains every full morphism, rather than just its underlying point map. -/
@[reassoc] theorem baseChangeSquare_natural {E F : GeneralizedEllipticCurve S} (a : E ⟶ F) :
    baseChangeMap t (baseChangeMap k a) ≫ ((baseChangeSquare s k t p h).app F).hom =
      ((baseChangeSquare s k t p h).app E).hom ≫ baseChangeMap p (baseChangeMap s a) :=
  (baseChangeSquare s k t p h).hom.naturality a

/-- Full comparisons obey the same commuting square as their original families. -/
theorem baseChangeSquare_natural_iso {E F : GeneralizedEllipticCurve S} (a : E ≅ F) :
    (baseChangeFunctor t).mapIso ((baseChangeFunctor k).mapIso a) ≪≫
      (baseChangeSquare s k t p h).app F =
    (baseChangeSquare s k t p h).app E ≪≫
      (baseChangeFunctor p).mapIso ((baseChangeFunctor s).mapIso a) :=
  Iso.ext (baseChangeSquare_natural s k t p h a.hom)

end FLT.Mazur.GeneralizedEllipticCurve
