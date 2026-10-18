/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRankThickenings
public import FLT.Mazur.RelativeExactRankFaithful

/-!
# Faithful full-source covers of original boundary rank coefficients

Every coefficient scheme on a positive original boundary rank stage has a
finite etale full-source cover. Compatible functions descend to that unchanged
scheme, and all its ideal-power equations are faithfully detected. These covers
are over individual stages, not over the entire original scalar boundary product.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
  chartBoundary chartBoundaryEndpoint rankPullbackMap rankPullbackThickening
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [LocallyQuasiFinite p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local instance stageDescentOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance stageDescentOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance stageDescentOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance stageDescentOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
variable (m k : ℕ) (hm : n ≤ m) {V : Scheme}
  (v : V ⟶ rankPullbackThickening (Over.mk p)
    (chartBoundaryEndpoint n o U e hU s κ) m k)
/-- The exact original endpoint of the retained rank-stage coefficients. -/
def boundaryStageCoefficientEndpoint : V ⟶ A :=
  v ≫ rankPullbackMap (Over.mk p) b m k ≫ b

local notation "c" => boundaryStageCoefficientEndpoint n o U e hU s κ m k v
local notation "π" => pullback.snd p c

omit [QuasiCompact p] [LocallyQuasiFinite p] in
/-- Every coefficient map retains the exact original rank, without reducing its scheme. -/
theorem boundaryStage_coefficient_exactRank : Set.range c ⊆ exactRank (Over.mk p) m := by
  rintro _ ⟨x, rfl⟩
  exact rankPullback_endpoint (Over.mk p) b m k (v x)

attribute [local irreducible] boundaryStageCoefficientEndpoint

/-- The whole original source over the retained coefficients is finite. -/
theorem boundaryStage_coefficient_source_finite : IsFinite π :=
  finite_pullback_of_exactRank (Over.mk p) m _
    (boundaryStage_coefficient_exactRank n o U e hU s κ m k v)

include hm in
/-- The original finite source is an actual descent cover of each coefficient scheme. -/
theorem boundaryStage_coefficient_source_effectiveEpi : EffectiveEpi π :=
  exactRank_source_effectiveEpi (Over.mk p) m ⟨o.val, lt_of_lt_of_le o.isLt hm⟩ _
    (boundaryStage_coefficient_exactRank n o U e hU s κ m k v)

include hm in
/-- Exact ideal-power equations descend, retaining every coefficient nilpotent. -/
theorem boundaryStage_coefficient_ideal_pow_iff (J : Ideal Γ(V, ⊤)) (l : ℕ) :
    (J.map (π).appTop.hom) ^ l = ⊥ ↔ J ^ l = ⊥ :=
  exactRank_source_ideal_pow_eq_bot_iff (Over.mk p) m ⟨o.val, lt_of_lt_of_le o.isLt hm⟩ _
    (boundaryStage_coefficient_exactRank n o U e hU s κ m k v) J l

include hm in
/-- Compatible full-source functions descend to the actual original rank coefficients. -/
theorem boundaryStage_coefficient_sections_existsUnique (t : Γ(pullback p c, ⊤))
    (ht : (pullback.fst π π).appTop t = (pullback.snd π π).appTop t) :
    ∃! u : Γ(V, ⊤), (π).appTop u = t := by
  let _ := boundaryStage_coefficient_source_effectiveEpi n o U e hU s κ m k hm v
  exact SchemeEffectiveEpiSections.sections_existsUnique (IsPullback.of_hasPullback π π) t ht

end FLT.Mazur.EquivalenceRelationNormalizedFrames
