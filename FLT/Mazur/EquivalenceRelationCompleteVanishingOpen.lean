/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteAdicSeparation
public import FLT.Mazur.SchemeAdicVanishingOpen

/-!
# An original relation open containing every complete first-endpoint fiber

One fixed ambient invariant coefficient equalizes the full original endpoints
on an actual open of the relation. Every arrow with complete first endpoint
lies in that open, with the second endpoint unrestricted inside the source.
This does not assert a source neighborhood whose entire relation lies there.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction FiniteGroupRestriction SchemeFiniteGroupQuotient
open SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
  (t : invariantCoordinates (restrictedAction (action e I o) U hU))
local notation "r" => SourceRestriction.fst U.ι U.ι
local notation "s" => SourceRestriction.snd U.ι U.ι
local notation "R" => SourceRestriction.relation U.ι U.ι

/-- The actual zero-germ open of the fixed full original discrepancy. -/
def completeRelationVanishingOpen : (R).Opens :=
  vanishingOpen ((r).appTop t.val - (s).appTop t.val)

omit [Etale p] in
/-- The constructed open equalizes the original coefficient with its whole nilpotent part. -/
theorem completeRelationVanishingOpen_equalizes :
    ((completeRelationVanishingOpen e I o U hU t).ι ≫ (r)).appTop t.val =
      ((completeRelationVanishingOpen e I o U hU t).ι ≫ (s)).appTop t.val := by
  have h := vanishingOpen_inclusion_zero ((r).appTop t.val - (s).appTop t.val)
  rw [map_sub, sub_eq_zero] at h
  simpa only [completeRelationVanishingOpen, Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply] using h

/-- The closed adic support is exactly the complete first-endpoint inverse image. -/
theorem completeRelationIdeal_support :
    ((completeRelationIdeal I o U).support : Set R) =
      ((r) ≫ U.ι) ⁻¹' completePointLocus (p := p) (q := q) I o := by
  rw [completeRelationIdeal, Scheme.IdealSheafData.support_comap]
  rfl

/-- All complete first-endpoint arrows belong to the same actual vanishing open. -/
theorem completeRelationVanishingOpen_contains [IsLocallyNoetherian A] :
    ((r) ≫ U.ι) ⁻¹' completePointLocus (p := p) (q := q) I o ⊆
      completeRelationVanishingOpen e I o U hU t := by
  let _ := completeRelation_locallyNoetherian e I o U
  rw [← completeRelationIdeal_support]
  exact support_subset_vanishingOpen _ (completeRelationIdeal I o U)
    (completeRelation_discrepancy_mem_pow e I o U hU t)

omit [Etale p] in
/-- Every scheme test through this original open satisfies the full original equation. -/
theorem completeRelationVanishingOpen_test {T : Scheme}
    (g : T ⟶ (completeRelationVanishingOpen e I o U hU t).toScheme) :
    (g ≫ (completeRelationVanishingOpen e I o U hU t).ι ≫ (r)).appTop t.val =
      (g ≫ (completeRelationVanishingOpen e I o U hU t).ι ≫ (s)).appTop t.val := by
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
    congrArg (fun x ↦ g.appTop x) (completeRelationVanishingOpen_equalizes e I o U hU t)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
