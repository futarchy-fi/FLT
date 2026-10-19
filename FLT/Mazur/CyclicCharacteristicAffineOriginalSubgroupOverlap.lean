/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOriginalSubgroupLocus
public import FLT.Mazur.CyclicCharacteristicAffineUniversalOverlap
public import FLT.Mazur.CompatibleSubgroupParameterRefinement
public import FLT.Mazur.FiniteSubgroupComparisonRefinement

/-!
# Original subgroup loci on the actual named affine overlaps

The full universal overlap identity identifies the closed subgroup locus
with its actual scheme pullback, on arbitrary scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassChangeParameter GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {A B : Type} [CommRing A] [CommRing B]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
  (q' : Spec (.of B) ⟶ normalizedLocus n b) (r' : Spec (.of B) ⟶ normalizedLocus n c)
  (f : A →+* B) (hq : q' = Spec.map (CommRingCat.ofHom f) ≫ q)
  (hr : r' = Spec.map (CommRingCat.ofHom f) ≫ r)
local notation "Q'" => EquationRing (affineEquation n b q') (affineEquation n c r')
local notation "k" => Spec.map (CommRingCat.ofHom f)
local notation "s" => affineComparisonStructure n b c q r
local notation "s'" => affineComparisonStructure n b c q' r'
local notation "m" => affineComparisonOverlapMap n b c q r q' r' f hq hr
local notation "t" => Spec.map (CommRingCat.ofHom (RingHom.comp (algebraMap B Q') f))
local notation "ht" => Spec.map_comp (CommRingCat.ofHom f)
  (CommRingCat.ofHom (algebraMap B Q'))
local notation "hm" => Eq.trans ht
  (Eq.symm (affineComparisonOverlapMap_structure n b c q r q' r' f hq hr))
local notation "a" => compatibleBaseChangeCompEq (normalizedSubgroup n b) q k q' hq
local notation "d" => compatibleBaseChangeCompEq (normalizedSubgroup n c) r k r' hr
local notation "ap" => compatibleParameterRefinement s m k s' t hm ht a
local notation "dp" => compatibleParameterRefinement s m k s' t hm ht d
local notation "e" => affineUniversalComparison n b c q r
local notation "e'" => affineUniversalComparison n b c q' r'

/-- The full named overlap is conjugation through actual compatible subgroup refinements. -/
theorem affineUniversalComparison_overlap_conjugate :
    e' = (ap).curve ≪≫ (baseChangeFunctor m).mapIso e ≪≫ (dp).curve.symm := by
  apply compatibleParameterRefinement_conjugate
  simpa only [compatibleBaseChangeCompEq_curve] using
    affineUniversalComparison_overlap n b c q r q' r' f hq hr

/-- The original-family closed subgroup locus is the actual named overlap pullback. -/
def affineOriginalSubgroupOverlapIso : affineOriginalSubgroupLocus n b c q' r' ≅
    pullback m (affineOriginalSubgroupInclusion n b c q r) :=
  subgroupComparisonRefinementIsoOfEq
    (((normalizedSubgroup n b).baseChange q).baseChange s)
    (((normalizedSubgroup n c).baseChange r).baseChange s) e m ap dp e'
    (affineUniversalComparison_overlap_conjugate n b c q r q' r' f hq hr)

/-- The pullback identifies the exact original refined closed immersion. -/
@[reassoc] theorem affineOriginalSubgroupOverlapIso_fst :
    (affineOriginalSubgroupOverlapIso n b c q r q' r' f hq hr).hom ≫ pullback.fst _ _ =
      affineOriginalSubgroupInclusion n b c q' r' :=
  subgroupComparisonRefinementIsoOfEq_fst
    (((normalizedSubgroup n b).baseChange q).baseChange s)
    (((normalizedSubgroup n c).baseChange r).baseChange s) e m ap dp e'
    (affineUniversalComparison_overlap_conjugate n b c q r q' r' f hq hr)

end FLT.Mazur.CyclicCharacteristicAtlas
