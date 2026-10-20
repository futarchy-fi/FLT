/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityGroupBaseChange
public import FLT.Mazur.TorusRootsOfUnitySubgroup
public import FLT.Mazur.GeneralizedCurveGeneratorTransport

/-!
# Original toric subgroups under arithmetic base change

The specified torus presentation pulls back as a group isomorphism, and its
roots-of-unity subgroup is identified with the actual original subgroup pullback.
Compatibility holds on the entire curve, retaining the subgroup divisor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GeneralizedEllipticCurve

open CharacterSchemeBaseChange RootsOfUnityInclusionBaseChange RootsOfUnityArithmeticPullback

variable {R : Type} [CommRing R] (E : GeneralizedEllipticCurve (Spec (.of R)))
  (e : MultiplicativeGroupScheme.gm R ≅ E.group) [IsMonHom e.hom]
  (A : Type) [CommRing A] [Algebra R A]

/-- The torus coordinates on the actual base-changed generalized curve. -/
def arithmeticTorusIso : MultiplicativeGroupScheme.gm A ≅ (E.baseChange (baseMap R A)).group :=
  torusComparison R A ≪≫ (Over.pullback (baseMap R A)).mapIso e

instance arithmeticTorusIso_isMonHom : IsMonHom (E.arithmeticTorusIso e A).hom := by
  dsimp only [arithmeticTorusIso, Iso.trans_hom, Functor.mapIso_hom]
  infer_instance

variable (n : ℕ) [NeZero n]

/-- The arithmetic subgroup comparison retains the original finite subgroup carrier. -/
def arithmeticSubgroupIso :
    ((E.baseChange (baseMap R A)).torusRootsOfUnitySubgroup (E.arithmeticTorusIso e A) n).carrier ≅
      ((E.torusRootsOfUnitySubgroup e n).baseChange (baseMap R A)).carrier :=
  comparison R A n

instance arithmeticSubgroupIso_isMonHom : IsMonHom (E.arithmeticSubgroupIso e A n).hom :=
  RootsOfUnityGroupBaseChange.roots_isMonHom R A n

/-- The compared subgroup inclusions agree on the actual whole curve after base change. -/
theorem arithmeticSubgroupIso_curveMap :
    ((E.baseChange (baseMap R A)).torusRootsOfUnitySubgroup
        (E.arithmeticTorusIso e A) n).curveMap =
      (E.arithmeticSubgroupIso e A n).hom ≫
        ((E.torusRootsOfUnitySubgroup e n).baseChange (baseMap R A)).curveMap := by
  rw [torusRootsOfUnitySubgroup_curveMap, FiniteSubgroup.baseChange_curveMap,
    torusRootsOfUnitySubgroup_curveMap, baseChange_inclusion]
  simp only [arithmeticTorusIso, arithmeticSubgroupIso, Iso.trans_hom, Functor.mapIso_hom,
    pullbackInclusion, Functor.map_comp, ← Category.assoc]
  rw [inclusion_comparison]

/-- A Cartier generator in extended torus coordinates generates the original subgroup pullback. -/
theorem arithmeticSubgroup_generator_transport
    {P : MonoidalCategory.tensorUnit (Over (Spec (.of A))) ⟶
      ((E.baseChange (baseMap R A)).torusRootsOfUnitySubgroup
        (E.arithmeticTorusIso e A) n).carrier}
    (hP : ((E.baseChange (baseMap R A)).torusRootsOfUnitySubgroup
      (E.arithmeticTorusIso e A) n).IsCartierGenerator P) :
    ((E.torusRootsOfUnitySubgroup e n).baseChange (baseMap R A)).IsCartierGenerator
      (P ≫ (E.arithmeticSubgroupIso e A n).hom) := by
  apply hP.transport _ _ (Iso.refl _) (E.arithmeticSubgroupIso e A n)
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact E.arithmeticSubgroupIso_curveMap e A n

end FLT.Mazur.GeneralizedEllipticCurve
