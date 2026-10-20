/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TorusRootsOfUnityTransport
public import FLT.Mazur.RootsOfUnityGroupBaseChange

/-!
# Full roots-of-unity subgroups commute with torus coefficient pullback

The actual character-algebra comparison preserves the root inclusion into the
entire curve. Its kernel ideal retains all infinitesimal multiplicities.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve

open CharacterSchemeBaseChange RootsOfUnityInclusionBaseChange

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (E : GeneralizedEllipticCurve (Spec (.of R)))
  (e : MultiplicativeGroupScheme.gm R ≅ E.group) [IsMonHom e.hom]
  (f : MultiplicativeGroupScheme.gm A ≅ (E.baseChange (baseMap R A)).group)
  [IsMonHom f.hom]
  (he : (torusComparison R A).hom ≫ (Over.pullback (baseMap R A)).map e.hom = f.hom)
  (n : ℕ) [NeZero n]

omit [IsMonHom f.hom] in
include he in
/-- The coefficient root comparison is compatible with the original smooth inclusion. -/
theorem torusRootsOfUnity_baseChange_inclusion :
    RootsOfUnityScheme.inclusion A n ≫ f.hom =
      (RootsOfUnityArithmeticPullback.comparison R A n).hom ≫
        ((E.torusRootsOfUnitySubgroup e n).baseChange (baseMap R A)).inclusion := by
  change RootsOfUnityScheme.inclusion A n ≫ f.hom =
    (RootsOfUnityArithmeticPullback.comparison R A n).hom ≫
      (Over.pullback (baseMap R A)).map (RootsOfUnityScheme.inclusion R n ≫ e.hom)
  rw [Functor.map_comp, ← Category.assoc, ← inclusion_comparison, Category.assoc, he]

/-- The whole pulled-back subgroup is the actual roots-of-unity subgroup in fiber coordinates. -/
def torusRootsOfUnityBaseChangeCompatibleIso : FiniteSubgroup.CompatibleIso
    ((E.baseChange (baseMap R A)).torusRootsOfUnitySubgroup f n)
    ((E.torusRootsOfUnitySubgroup e n).baseChange (baseMap R A)) where
  curve := Iso.refl _
  subgroup := RootsOfUnityArithmeticPullback.comparison R A n
  isMonHom := RootsOfUnityGroupBaseChange.roots_isMonHom R A n
  compatible := by
    change (_ ≫ _) ≫ 𝟙 _ = _ ≫ (_ ≫ _)
    rw [Category.comp_id, ← Category.assoc]
    exact congrArg (· ≫ (E.baseChange (baseMap R A)).inclusion)
      (torusRootsOfUnity_baseChange_inclusion E e f he n)

include he in
/-- The full ideal agrees with the base change of the original root ideal. -/
theorem torusRootsOfUnity_baseChange_ideal_eq :
    ((E.baseChange (baseMap R A)).torusRootsOfUnitySubgroup f n).ideal =
      ((E.torusRootsOfUnitySubgroup e n).baseChange (baseMap R A)).ideal := by
  let h := torusRootsOfUnityBaseChangeCompatibleIso E e f he n
  have hi := FiniteSubgroup.ideal_transport _ _ h.curve h.subgroup h.compatible
  change _ = ((E.baseChange (baseMap R A)).torusRootsOfUnitySubgroup f n).ideal.comap
    (𝟙 _) at hi
  simpa only [Scheme.IdealSheafData.comap_id] using hi.symm

end FLT.Mazur.GeneralizedEllipticCurve
