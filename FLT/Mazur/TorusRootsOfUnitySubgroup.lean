/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityScheme
public import FLT.Mazur.GeneralizedCurveSubgroupIdeal

/-!
# Roots-of-unity subgroups in toric generalized curves

An actual torus presentation of the smooth group transports the constructed
roots-of-unity scheme into a finite subgroup of the full generalized curve.
The subgroup ideal and its arbitrary base changes retain the original inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {R : Type} [CommRing R] (E : GeneralizedEllipticCurve (Spec (.of R)))
  (e : MultiplicativeGroupScheme.gm R ≅ E.group) [IsMonHom e.hom]
  (n : ℕ) [NeZero n]

/-- The actual roots-of-unity carrier as a subgroup of a toric generalized curve. -/
def torusRootsOfUnitySubgroup : E.FiniteSubgroup n where
  carrier := RootsOfUnityScheme.model R n
  inclusion := RootsOfUnityScheme.inclusion R n ≫ e.hom
  closed := by
    let _ : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    change IsClosedImmersion ((RootsOfUnityScheme.inclusion R n).left ≫ e.hom.left)
    infer_instance
  degree := RootsOfUnityScheme.degree R n

/-- The subgroup inclusion retains the specified torus coordinate. -/
theorem torusRootsOfUnitySubgroup_inclusion :
    (E.torusRootsOfUnitySubgroup e n).inclusion =
      RootsOfUnityScheme.inclusion R n ≫ e.hom := rfl

/-- The whole-curve map is the original root inclusion followed by the torus open. -/
theorem torusRootsOfUnitySubgroup_curveMap :
    (E.torusRootsOfUnitySubgroup e n).curveMap =
      RootsOfUnityScheme.inclusion R n ≫ e.hom ≫ E.inclusion :=
  Category.assoc _ _ _

/-- Its ideal is the kernel of that actual map, not just its reduced support. -/
theorem torusRootsOfUnitySubgroup_ideal :
    (E.torusRootsOfUnitySubgroup e n).ideal =
      ((RootsOfUnityScheme.inclusion R n).left ≫ e.hom.left ≫ E.inclusion.left).ker := by
  rw [FiniteSubgroup.ideal, torusRootsOfUnitySubgroup_curveMap]
  rfl

/-- The whole-curve closed subscheme has finite locally free degree n. -/
theorem torusRootsOfUnitySubgroup_ideal_degree :
    FCurve.FiniteLocallyFreeDegree
      ((E.torusRootsOfUnitySubgroup e n).ideal.subschemeι ≫ E.curve.hom) n :=
  (E.torusRootsOfUnitySubgroup e n).ideal_degree

/-- All scheme base changes retain the full subgroup ideal, including infinitesimal tests. -/
theorem torusRootsOfUnitySubgroup_baseChange_ideal {T : Scheme}
    (g : T ⟶ Spec (.of R)) :
    ((E.torusRootsOfUnitySubgroup e n).baseChange g).ideal =
      (E.torusRootsOfUnitySubgroup e n).ideal.comap (pullback.fst E.curve.hom g) :=
  (E.torusRootsOfUnitySubgroup e n).baseChange_ideal g

end FLT.Mazur.GeneralizedEllipticCurve
