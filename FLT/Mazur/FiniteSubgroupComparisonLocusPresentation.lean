/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSubgroupComparisonLocus
public import FLT.Mazur.CompatibleSubgroupIsoConjugation

/-!
# Closed comparison loci retain compatible subgroup presentations

Changing the two original subgroup presentations gives an actual isomorphism
of their closed comparison schemes over the unchanged base. This applies to
every scheme test and does not impose a generator marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {n : ℕ} {E F E' F' : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
  {H' : E'.FiniteSubgroup n} {J' : F'.FiniteSubgroup n}
  (a : CompatibleIso H H') (b : CompatibleIso J J') (e : E ≅ F)
local notation "e'" => a.curve.symm ≪≫ e ≪≫ b.curve
local notation "i" => subgroupComparisonLocusInclusion H J e
local notation "j" => subgroupComparisonLocusInclusion H' J' e'

/-- Changing compatible presentations preserves the full subgroup condition on every test. -/
theorem subgroupComparisonLocus_factorization_presentation_iff {T : Scheme} (g : T ⟶ S) :
    (∃ k : T ⟶ subgroupComparisonLocus H J e, k ≫ i = g) ↔
      ∃ k : T ⟶ subgroupComparisonLocus H' J' e', k ≫ j = g := by
  rw [subgroupComparisonLocus_factorization_iff, subgroupComparisonLocus_factorization_iff]
  simpa only [CompatibleIso.baseChange, transportCompatibleIso,
    Functor.mapIso_trans, Functor.mapIso_symm] using
    compatibleIso_exists_conjugate_iff (a.baseChange g) (b.baseChange g)
      ((baseChangeFunctor g).mapIso e)

/-- Compatible presentations construct a map between the actual closed comparison loci. -/
def subgroupComparisonLocusPresentationMap :
    subgroupComparisonLocus H J e ⟶ subgroupComparisonLocus H' J' e' :=
  ((subgroupComparisonLocus_factorization_presentation_iff a b e i).mp
    ⟨𝟙 _, Category.id_comp _⟩).choose

/-- The comparison of closed loci retains the original closed immersion into the base. -/
@[reassoc] theorem subgroupComparisonLocusPresentationMap_inclusion :
    subgroupComparisonLocusPresentationMap a b e ≫ j = i :=
  ((subgroupComparisonLocus_factorization_presentation_iff a b e i).mp
    ⟨𝟙 _, Category.id_comp _⟩).choose_spec

/-- The closed comparison scheme is invariant under compatible full subgroup presentations. -/
def subgroupComparisonLocusPresentationIso :
    subgroupComparisonLocus H J e ≅ subgroupComparisonLocus H' J' e' := by
  let f := subgroupComparisonLocusPresentationMap a b e
  have hf : f ≫ j = i := subgroupComparisonLocusPresentationMap_inclusion a b e
  let hg := (subgroupComparisonLocus_factorization_presentation_iff a b e j).mpr
    ⟨𝟙 _, Category.id_comp _⟩
  exact
    { hom := f
      inv := hg.choose
      hom_inv_id := by
        apply (cancel_mono i).mp
        rw [Category.assoc, hg.choose_spec, hf, Category.id_comp]
      inv_hom_id := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hf, hg.choose_spec, Category.id_comp] }

/-- The scheme isomorphism keeps the exact original parameter map. -/
@[reassoc] theorem subgroupComparisonLocusPresentationIso_inclusion :
    (subgroupComparisonLocusPresentationIso a b e).hom ≫ j = i :=
  subgroupComparisonLocusPresentationMap_inclusion a b e

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
