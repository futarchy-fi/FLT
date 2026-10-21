/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryGlobalDifferentialLift
public import FLT.Mazur.OriginalBoundaryDifferentialOpenNaturality
public import FLT.Mazur.OriginalBoundaryGenericRankCoverage
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Compatible differential-open arrows on all original rank orders

Generic coverage at one order supplies point coverage on every order.
Constructed full endpoint finiteness and the actual differential open then
produce unique original arrows. Their restrictions along the original stage
transitions agree, including the entire nonreduced coefficient structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian A] [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance rankDifferentialOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankDifferentialOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankDifferentialOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance rankDifferentialBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism
variable (t : B ⟶ pullback
  (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
  (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
local notation "v" n:max k:max => rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t
local notation "U" n:max k:max => originalBoundaryDifferentialOpen J (v n k)

include e in
/-- One order of generic coverage constructs actual differential-open arrows at all orders. -/
theorem originalBoundary_rankDifferentialOpen_lift (k₀ : ℕ)
    (h : ∀ n, genericPoints (rankPullbackThickening (Over.mk p) (t ≫ x) n k₀) ⊆
      (v n k₀) ⁻¹' Set.range c) (n k : ℕ) :
    ∃! d : (U n k).toScheme ⟶ pullback p J.subschemeι, d ≫ c = (U n k).ι ≫ v n k := by
  let _ : IsLocallyNoetherian (rankPullbackThickening (Over.mk p) (t ≫ x) n k) :=
    LocallyOfFiniteType.isLocallyNoetherian (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  apply originalBoundary_localNoetherian_differentialOpen_lift e J hJ
  rintro _ ⟨u, rfl⟩
  exact originalBoundary_coverage_of_generic_rankStages J hJ t k₀ h
    (Set.mem_range_self (rankPullbackMap (Over.mk p) (t ≫ x) n k u))

/-- The canonical infinitesimal transition restricts to the full differential opens. -/
def originalBoundaryRankDifferentialTransition (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    (U n k).toScheme ⟶ (U n l).toScheme :=
  (rankStagePullbackTransition (Over.mk p) (t ≫ x) n h).resLE _ _ (by
    rw [← originalBoundary_differentialOpen_precompose,
      rankStagePullbackTransition_map_assoc])

omit e [IsAffine A] [QuasiCompact p] [LocallyQuasiFinite p] [IsLocallyNoetherian A]
  [IsLocallyNoetherian B] in
/-- Restricted transitions preserve the original full coefficient map. -/
@[reassoc]
theorem originalBoundaryRankDifferentialTransition_ι (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    originalBoundaryRankDifferentialTransition J t n h ≫ (U n l).ι =
      (U n k).ι ≫ rankStagePullbackTransition (Over.mk p) (t ≫ x) n h :=
  Scheme.Hom.resLE_comp_ι _ _

include e in
omit [IsAffine A] [QuasiCompact p] [LocallyQuasiFinite p] [IsLocallyNoetherian A]
  [IsLocallyNoetherian B] in
/-- All full differential-open arrows agree under the actual original stage transitions. -/
theorem originalBoundary_rankDifferentialOpen_compatible (n : ℕ) {k l : ℕ} (h : k ≤ l)
    (d : (U n k).toScheme ⟶ pullback p J.subschemeι)
    (d' : (U n l).toScheme ⟶ pullback p J.subschemeι)
    (hd : d ≫ c = (U n k).ι ≫ v n k) (hd' : d' ≫ c = (U n l).ι ≫ v n l) :
    originalBoundaryRankDifferentialTransition J t n h ≫ d' = d := by
  let _ := originalBoundaryComparison_mono e J hJ
  apply (cancel_mono c).mp
  simp only [Category.assoc, hd, hd', originalBoundaryRankDifferentialTransition_ι_assoc,
    rankStagePullbackTransition_map_assoc]

end FLT.Mazur.EquivalenceRelationOrderedFrames
