/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSeedSelectorGeometry
public import FLT.Mazur.RelativeRelationOrbitOpens

/-!
# Constructing representatives on invariant subopens

An original representative stays in every invariant open containing its
source. Thus a selector on an open constructs selectors on all invariant
subopens, including intersections with other independently selected charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSeedSelector.Data
open RelativeRelationOrbit SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  {U : A.left.Opens} (d : Data p q U.ι)
  (V : InvariantOpens p q) (h : V.val ≤ U)
local notation "j" => A.left.homOfLE h

/-- Original arrows keep selected representatives inside every invariant subopen. -/
theorem rep_mem (x : V.val.toScheme) : U.ι (d.rep (j x)) ∈ V.val := by
  apply (invariant_mem_iff V (d.related_representative (j x))).mp
  have hx : U.ι (j x) = x.val := congrArg (fun a ↦ a x) (Scheme.homOfLE_ι A.left h)
  rw [hx]
  exact x.property

/-- The restricted endomorphism is constructed by the open-immersion lifting property. -/
def restrictedRep : V.val.toScheme ⟶ V.val.toScheme :=
  IsOpenImmersion.lift V.val.ι (j ≫ d.rep ≫ U.ι) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, d.rep_mem V h x⟩, rfl⟩)

@[reassoc]
theorem restrictedRep_ι : d.restrictedRep V h ≫ V.val.ι = j ≫ d.rep ≫ U.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- On the old seed, this is exactly the old representative endomorphism. -/
@[reassoc]
theorem restrictedRep_inclusion : d.restrictedRep V h ≫ j = j ≫ d.rep := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, restrictedRep_ι, Category.assoc]

/-- The original arrows and their full invariance restrict to the smaller invariant open. -/
def restrict : Data p q V.val.ι where
  rep := d.restrictedRep V h
  arrow := j ≫ d.arrow
  source := by rw [Category.assoc, d.source, Scheme.homOfLE_ι]
  target := by rw [Category.assoc, d.target, restrictedRep_ι]
  invariant := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, restrictedRep_inclusion]
    apply d.on_arrow (SchemeRelationRestriction.arrow p.left q.left V.val.ι)
      (fst p.left q.left V.val.ι ≫ j) (snd p.left q.left V.val.ι ≫ j)
    · rw [Category.assoc, Scheme.homOfLE_ι, arrow_fst]
    · rw [Category.assoc, Scheme.homOfLE_ι, arrow_snd]

/-- The restriction quotient embeds openly into the original selector quotient. -/
theorem restrict_map_isOpenImmersion (e : CategoryTheory.EquivalenceRelation p q)
    [Etale q.left] : IsOpenImmersion ((d.restrict V h).map d j) :=
  (d.restrict V h).map_isOpenImmersion e d j (Scheme.homOfLE_ι A.left h)

end FLT.Mazur.SchemeRelationSeedSelector.Data
