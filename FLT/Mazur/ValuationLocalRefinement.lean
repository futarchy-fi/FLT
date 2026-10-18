/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ValuationResidueRefinement

/-!
# Refining a valuation to the exact local scalar center

A local scalar ring mapping into a valuation may have a strictly smaller center.
Dominate its image in the residue field and pull that valuation back. The refined
valuation retains all scalars, has the exact center, and preserves every pole.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ValuationResidueRefinement
open IsLocalRing
variable {K R : Type*} [Field K] [CommRing R]
  (V : ValuationSubring K) (W : ValuationSubring (ResidueField V))

/-- The residue map from the refined valuation to the residue valuation. -/
def refinementResidue : refinement V W →+* W :=
  ((residue V).comp (Subring.inclusion (refinement_le V W))).codRestrict
    W.toSubring (fun x ↦ by
      obtain ⟨a, ha, hr⟩ := (mem_refinementRing V W x.val).mp x.property
      change residue V ⟨x.val, _⟩ ∈ W
      convert hr using 1
      exact congrArg (residue V) (Subtype.ext ha.symm))

variable (f : R →+* V) (hf : ∀ a, residue V (f a) ∈ W)

/-- The original scalar map, with values in the refined valuation. -/
def refinementScalar : R →+* refinement V W :=
  (V.subtype.comp f).codRestrict (refinement V W).toSubring
    (fun a ↦ (mem_refinementRing V W _).mpr ⟨f a, rfl, hf a⟩)

/-- Refinement preserves the entire scalar map in the original ambient field. -/
theorem refinementScalar_comp :
    (refinement V W).subtype.comp (refinementScalar V W f hf) = V.subtype.comp f := rfl

/-- The residue square commutes with the unchanged scalar coordinates. -/
theorem refinementResidue_comp :
    (refinementResidue V W).comp (refinementScalar V W f hf) =
      ((residue V).comp f).codRestrict W.toSubring hf := rfl

/-- Locality of the residue scalar map forces locality of the refined scalar map. -/
theorem refinementScalar_isLocalHom
    (hl : IsLocalHom (((residue V).comp f).codRestrict W.toSubring hf)) :
    IsLocalHom (refinementScalar V W f hf) := by
  constructor
  intro a ha
  apply hl.map_nonunit a
  exact ha.map (refinementResidue V W)

variable [IsLocalRing R]

/-- Every scalar-containing valuation has a refinement with the exact local scalar center. -/
theorem exists_local_refinement (f : R →+* V) :
    ∃ (V' : ValuationSubring K), V' ≤ V ∧ ∃ f' : R →+* V',
      V'.subtype.comp f' = V.subtype.comp f ∧ IsLocalHom f' := by
  obtain ⟨W, hf, hl⟩ := exists_factor_valuationRing ((residue V).comp f)
  exact ⟨refinement V W, refinement_le V W, refinementScalar V W f hf,
    refinementScalar_comp V W f hf, refinementScalar_isLocalHom V W f hf hl⟩

/-- The refinement retains any specified pole, while making the scalar map local. -/
theorem exists_local_refinement_with_pole (f : R →+* V) (x : K) (hx : x ∉ V) :
    ∃ (V' : ValuationSubring K) (f' : R →+* V'),
      V'.subtype.comp f' = V.subtype.comp f ∧ IsLocalHom f' ∧ x ∉ V' := by
  obtain ⟨V', hle, f', hf', hl⟩ := exists_local_refinement V f
  exact ⟨V', f', hf', hl, fun h ↦ hx (hle h)⟩

end FLT.Mazur.ValuationResidueRefinement
