/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSubgroupComparisonLocusBaseChange
public import FLT.Mazur.FiniteSubgroupComparisonLocusPresentation

/-!
# Closed comparison loci under compatible refinement

A compatible change of presentation after base change identifies the entire
closed subgroup locus with the original scheme pullback.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {E' F' : GeneralizedEllipticCurve T}
  (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n) (e : E ≅ F) (g : T ⟶ S)
  {H' : E'.FiniteSubgroup n} {J' : F'.FiniteSubgroup n}
  (a : CompatibleIso H' (H.baseChange g)) (b : CompatibleIso J' (J.baseChange g))
local notation "e'" => a.curve ≪≫ Functor.mapIso (baseChangeFunctor g) e ≪≫ b.curve.symm
local notation "i" => subgroupComparisonLocusInclusion H J e
local notation "i'" => subgroupComparisonLocusInclusion H' J' e'

/-- Compatible refinements identify the actual closed subgroup schemes over the new base. -/
def subgroupComparisonRefinementIso :
    subgroupComparisonLocus H' J' e' ≅ pullback g i :=
  (subgroupComparisonLocusPresentationIso a.symm b.symm
    ((baseChangeFunctor g).mapIso e)).symm ≪≫ subgroupComparisonLocusBaseChangeIso H J e g

/-- The closed immersion is exactly the first projection of the scheme pullback. -/
@[reassoc] theorem subgroupComparisonRefinementIso_fst :
    (subgroupComparisonRefinementIso H J e g a b).hom ≫ pullback.fst _ _ = i' := by
  rw [subgroupComparisonRefinementIso, Iso.trans_hom, Category.assoc,
    subgroupComparisonLocusBaseChangeIso_fst]
  apply (Iso.inv_comp_eq _).mpr
  exact (subgroupComparisonLocusPresentationIso_inclusion a.symm b.symm
    ((baseChangeFunctor g).mapIso e)).symm

/-- Both projections of the refined locus form the original closed-locus base square. -/
@[reassoc] theorem subgroupComparisonRefinementIso_square :
    (subgroupComparisonRefinementIso H J e g a b).hom ≫ pullback.snd _ _ ≫ i = i' ≫ g := by
  rw [← pullback.condition, ← Category.assoc, subgroupComparisonRefinementIso_fst]

/-- A separately constructed refined comparison gives the same closed-locus pullback. -/
def subgroupComparisonRefinementIsoOfEq (e₁ : E' ≅ F') (he : e₁ = e') :
    subgroupComparisonLocus H' J' e₁ ≅ pullback g i := by
  subst e₁
  exact subgroupComparisonRefinementIso H J e g a b

/-- The named refined comparison retains its exact closed immersion under the identification. -/
@[reassoc] theorem subgroupComparisonRefinementIsoOfEq_fst (e₁ : E' ≅ F') (he : e₁ = e') :
    (subgroupComparisonRefinementIsoOfEq H J e g a b e₁ he).hom ≫ pullback.fst _ _ =
      subgroupComparisonLocusInclusion H' J' e₁ := by
  subst e₁
  exact subgroupComparisonRefinementIso_fst H J e g a b

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
