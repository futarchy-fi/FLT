/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureZero

/-!
# The actual product of the subgroup closure

The product is formed over the valuation ring, with the actual integral
subgroup sections and the comparison into the original cubic product.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- The fiber product of the actual glued subgroup closure with itself. -/
abbrev closureProduct : Scheme :=
  pullback (closureToBase A W H 1 2) (closureToBase A W H 1 2)

/-- A pair of actual integral subgroup sections in the fiber product. -/
def closureSectionPair (P Q : H) : Spec (.of A) ⟶ closureProduct A W H :=
  pullback.lift (integralSection A W H P) (integralSection A W H Q)
    (by rw [integralSection_toBase, integralSection_toBase])

/-- First projection of the actual section pair. -/
@[reassoc] theorem closureSectionPair_fst (P Q : H) :
    closureSectionPair A W H P Q ≫ pullback.fst _ _ = integralSection A W H P :=
  pullback.lift_fst _ _ _

/-- Second projection of the actual section pair. -/
@[reassoc] theorem closureSectionPair_snd (P Q : H) :
    closureSectionPair A W H P Q ≫ pullback.snd _ _ = integralSection A W H Q :=
  pullback.lift_snd _ _ _

/-- The comparison of actual closure products with the ambient cubic product. -/
def closureProductToCurve : closureProduct A W H ⟶ integralCurveProduct W :=
  pullback.map _ _ _ _ (closureToCurve A W H 1 2) (closureToCurve A W H 1 2)
    (𝟙 _) (by rw [Category.comp_id, closureToCurve_structure])
    (by rw [Category.comp_id, closureToCurve_structure])

/-- The comparison retains the first original closed immersion. -/
@[reassoc] theorem closureProductToCurve_fst :
    closureProductToCurve A W H ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ closureToCurve A W H 1 2 := pullback.lift_fst _ _ _

/-- The comparison retains the second original closed immersion. -/
@[reassoc] theorem closureProductToCurve_snd :
    closureProductToCurve A W H ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ closureToCurve A W H 1 2 := pullback.lift_snd _ _ _

/-- Closure section pairs are the prescribed ambient section pairs. -/
@[reassoc] theorem closureSectionPair_toCurve (P Q : H) :
    closureSectionPair A W H P Q ≫ closureProductToCurve A W H =
      ambientSectionPair A W H P Q := by
  apply pullback.hom_ext
  · rw [Category.assoc, closureProductToCurve_fst, closureSectionPair_fst_assoc,
      ambientSectionPair_fst]
  · rw [Category.assoc, closureProductToCurve_snd, closureSectionPair_snd_assoc,
      ambientSectionPair_snd]

/-- All integral sections collected as a single actual morphism. -/
def closureSectionsMap : (∐ fun _ : H => Spec (.of A)) ⟶ gluedClosure A W H 1 2 :=
  Sigma.desc (integralSection A W H)

/-- Its restriction to each summand is the original integral section. -/
@[reassoc] theorem closureSectionsMap_point (P : H) :
    Sigma.ι (fun _ : H => Spec (.of A)) P ≫ closureSectionsMap A W H =
      integralSection A W H P := Sigma.ι_comp_desc _ _

/-- The structural map of the section family is the coproduct of identity maps. -/
theorem closureSectionsMap_toBase :
    closureSectionsMap A W H ≫ closureToBase A W H 1 2 =
      Sigma.desc (fun _ : H => 𝟙 (Spec (.of A))) := by
  apply Sigma.hom_ext
  intro P
  rw [closureSectionsMap_point_assoc, integralSection_toBase, Sigma.ι_comp_desc]

/-- All pairs of integral subgroup sections collected into one morphism. -/
def closureSectionPairsMap : (∐ fun _ : H × H => Spec (.of A)) ⟶ closureProduct A W H :=
  Sigma.desc (fun PQ => closureSectionPair A W H PQ.1 PQ.2)

/-- Each summand is precisely the corresponding pair of original sections. -/
@[reassoc] theorem closureSectionPairsMap_point (P Q : H) :
    Sigma.ι (fun _ : H × H => Spec (.of A)) (P, Q) ≫ closureSectionPairsMap A W H =
      closureSectionPair A W H P Q := Sigma.ι_comp_desc _ _

end FLT.Mazur.EllipticSubgroupChart
