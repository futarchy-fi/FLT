/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismOpenSource
public import FLT.Mazur.SchemeRelationSplitOrbitQuotient
public import FLT.Mazur.SchemeEtaleImageQuotient

/-!
# Genuine open parameter selections of original split orbits

A monic orbit map into the actual parameter scheme constructs an open
parameter chart and an etale quotient onto its actual seed image. No old
unramifiedness is assumed. The precise open of retained reflexive seeds is
constructed; its nonemptiness is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOrbitOpenSelection
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S Z H : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (a : Z ⟶ A.left)
  (j : pullback q.left a ⟶ H) [Mono j]
local notation "B" => (pullback q.left a : Scheme)
local notation "π" => pullback.snd q.left a
local notation "U" => MonomorphismOpenImage.locus j
local notation "l" => MonomorphismOpenImage.lift j

/-- This is an actual open of the parameter scheme, not just an immersed source. -/
abbrev parameterOpen : H.Opens := U

/-- The original orbit projection restricted to the constructed open chart. -/
def projection : (parameterOpen a j).toScheme ⟶ Z := l ≫ π

instance projection_etale [Etale q.left] : Etale (projection a j) :=
  inferInstanceAs (Etale (l ≫ π))

/-- The retained seed domain is an actual open of the unchanged seed scheme. -/
def seedOpen : Z.Opens :=
  SchemeRelationSplitOrbit.sectionMap e a ⁻¹ᵁ MonomorphismOpenImage.sourceOpen j

/-- Restrict the actual reflexive section to the constructed open parameter chart. -/
def seed : (seedOpen e a j).toScheme ⟶ (parameterOpen a j).toScheme :=
  IsOpenImmersion.lift (U).ι
    ((seedOpen e a j).ι ≫ SchemeRelationSplitOrbit.sectionMap e a ≫ j) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.property)

omit [Mono j] in
@[reassoc]
theorem seed_parameter : seed e a j ≫ (parameterOpen a j).ι =
    (seedOpen e a j).ι ≫ SchemeRelationSplitOrbit.sectionMap e a ≫ j :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem seed_orbit : seed e a j ≫ l =
    (seedOpen e a j).ι ≫ SchemeRelationSplitOrbit.sectionMap e a := by
  apply (cancel_mono j).mp
  rw [Category.assoc, MonomorphismOpenImage.lift_comp, seed_parameter, Category.assoc]

@[reassoc]
theorem seed_projection : seed e a j ≫ projection a j = (seedOpen e a j).ι := by
  rw [projection, ← Category.assoc, seed_orbit, Category.assoc,
    SchemeRelationSplitOrbit.sectionMap_projection, Category.comp_id]

/-- The selected seed is itself open in the selected parameters. -/
theorem seed_isOpenImmersion [Etale q.left] : IsOpenImmersion (seed e a j) := by
  let _ : IsOpenImmersion (seed e a j ≫ projection a j) := by
    rw [seed_projection]
    infer_instance
  let _ : Etale (seed e a j) := Etale.of_comp _ (projection a j)
  let _ : Mono (seed e a j) := mono_of_mono (seed e a j) (projection a j)
  exact IsOpenImmersion.of_flat_of_mono _

/-- Exact seed coverage criterion in the original orbit, with the actual parameter map. -/
theorem mem_seedOpen_iff (z : Z) : z ∈ seedOpen e a j ↔
    ∃ (Y : Scheme) (b : Y ⟶ B) (y : Y),
      IsOpenImmersion b ∧ IsOpenImmersion (b ≫ j) ∧
        b y = SchemeRelationSplitOrbit.sectionMap e a z :=
  MonomorphismOpenImage.mem_sourceOpen_iff j (SchemeRelationSplitOrbit.sectionMap e a z)

variable [Etale q.left]

/-- The quotient keeps exactly the seed image reached by the complete selected source. -/
def targetOpen : Z.Opens := SchemeEtaleImageQuotient.image (projection a j)

/-- The constructed quotient is surjective etale onto its actual open target. -/
def quotient : (parameterOpen a j).toScheme ⟶ (targetOpen a j).toScheme :=
  SchemeEtaleImageQuotient.projection (projection a j)

instance quotient_etale : Etale (quotient a j) :=
  inferInstanceAs (Etale (SchemeEtaleImageQuotient.projection (projection a j)))
instance quotient_surjective : Surjective (quotient a j) :=
  inferInstanceAs (Surjective (SchemeEtaleImageQuotient.projection (projection a j)))

@[reassoc]
theorem quotient_ι : quotient a j ≫ (targetOpen a j).ι = projection a j :=
  SchemeEtaleImageQuotient.projection_ι (projection a j)

/-- Every retained reflexive seed belongs to the constructed quotient target. -/
theorem seedOpen_le_targetOpen : seedOpen e a j ≤ targetOpen a j := by
  intro z hz
  exact ⟨seed e a j ⟨z, hz⟩,
    congrArg (fun g ↦ g ⟨z, hz⟩) (seed_projection e a j)⟩

end FLT.Mazur.SchemeOrbitOpenSelection
