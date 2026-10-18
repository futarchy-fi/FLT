/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSubgroupEqualityLocus
public import FLT.Mazur.RetainedSubgroupCartierMarking
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# The closed locus extending a prescribed full curve comparison

Given an actual full curve isomorphism, the equality locus of the transported
subgroup and the target subgroup represents its extension to a compatible
subgroup isomorphism. This constructs the subgroup condition in the full
unmarked relation; a parameter scheme for varying curve isomorphisms is
still separate work. No generator or etaleness assumption is required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}

/-- The comparison constructed from equal ideals retains the identical full curve. -/
theorem compatibleIsoOfIdealEq_curve_refl (H J : E.FiniteSubgroup n) (h : H.ideal = J.ideal) :
    (compatibleIsoOfIdealEq H J h).curve = Iso.refl E := rfl

/-- A compatible comparison with the identical whole curve forces equality of the actual ideals. -/
theorem CompatibleIso.ideal_eq_of_curve_refl {H J : E.FiniteSubgroup n}
    (a : CompatibleIso H J) (ha : a.curve = Iso.refl E) : H.ideal = J.ideal := by
  let _ : IsIso a.subgroup.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).mapIso a.subgroup).hom)
  have he := congrArg Over.Hom.left a.compatible
  rw [ha] at he
  change H.curveMap.left ≫ 𝟙 _ = a.subgroup.hom.left ≫ J.curveMap.left at he
  rw [Category.comp_id] at he
  change H.curveMap.left.ker = J.curveMap.left.ker
  rw [he, Scheme.Hom.ker_comp_of_isIso]

variable (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n) (e : E ≅ F)

/-- The actual closed parameter scheme where the prescribed full comparison preserves subgroups. -/
def subgroupComparisonLocus : Scheme := equalityLocus (H.transport e) J

/-- The comparison locus retains its actual original parameter map. -/
def subgroupComparisonLocusInclusion : subgroupComparisonLocus H J e ⟶ S :=
  equalityLocusInclusion (H.transport e) J

instance subgroupComparisonLocusInclusion_closed :
    IsClosedImmersion (subgroupComparisonLocusInclusion H J e) :=
  inferInstanceAs (IsClosedImmersion (equalityLocusInclusion (H.transport e) J))

/-- The closed locus represents actual compatible extensions of the prescribed curve comparison. -/
theorem subgroupComparisonLocus_factorization_iff {T : Scheme} (g : T ⟶ S) :
    (∃ k : T ⟶ subgroupComparisonLocus H J e,
      k ≫ subgroupComparisonLocusInclusion H J e = g) ↔
      ∃ a : CompatibleIso (H.baseChange g) (J.baseChange g),
        a.curve = ((H.transportCompatibleIso e).baseChange g).curve := by
  change (∃ k : T ⟶ equalityLocus (H.transport e) J,
    k ≫ equalityLocusInclusion (H.transport e) J = g) ↔ _
  rw [equalityLocus_factorization_iff]
  let a₀ := (H.transportCompatibleIso e).baseChange g
  constructor
  · intro h
    refine ⟨a₀.trans (compatibleIsoOfIdealEq _ _ h), ?_⟩
    change a₀.curve ≪≫ (compatibleIsoOfIdealEq _ _ h).curve = a₀.curve
    simp only [compatibleIsoOfIdealEq_curve_refl, Iso.trans_refl]
  · rintro ⟨a, ha⟩
    apply (a₀.symm.trans a).ideal_eq_of_curve_refl
    change a₀.curve.symm ≪≫ a.curve = Iso.refl _
    rw [ha]
    exact a₀.curve.symm_self_id

/-- The original full curves and subgroups compare genuinely over the constructed locus. -/
def subgroupComparisonLocusCompatibleIso :
    CompatibleIso (H.baseChange (subgroupComparisonLocusInclusion H J e))
      (J.baseChange (subgroupComparisonLocusInclusion H J e)) :=
  ((H.transportCompatibleIso e).baseChange (subgroupComparisonLocusInclusion H J e)).trans
    (equalityLocusCompatibleIso (H.transport e) J)

/-- The universal subgroup comparison retains the originally specified full curve comparison. -/
theorem subgroupComparisonLocusCompatibleIso_curve :
    (subgroupComparisonLocusCompatibleIso H J e).curve =
      ((H.transportCompatibleIso e).baseChange (subgroupComparisonLocusInclusion H J e)).curve := by
  change _ ≪≫ (compatibleIsoOfIdealEq _ _ _).curve = _
  simp only [compatibleIsoOfIdealEq_curve_refl, Iso.trans_refl]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
