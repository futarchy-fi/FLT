/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryFrameUnits

/-!
# The four normalization equations on the original auxiliary base

The quotient imposes exactly the normalized frame equations on the global
functions of the full auxiliary scheme. Its spectrum will be pulled back to
that original scheme; no affineness of the auxiliary scheme is assumed here.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.UniversalWeierstrass

/-- The four actual functions cutting out the normalized frame. -/
def normalizedSliceRelation : Fin 4 → AuxiliarySectionRing :=
  ![auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 0,
    auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 1,
    auxiliaryCoordinate frameLabelThird frameLabelThird_ne 1,
    auxiliaryCoordinate frameLabelThird frameLabelThird_ne 0 -
      auxiliaryCoordinate frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne) 1]

/-- The ideal of the four frame equations in actual auxiliary global functions. -/
def normalizedSliceIdeal : Ideal AuxiliarySectionRing :=
  Ideal.span (Set.range normalizedSliceRelation)

/-- The ring imposing the normalization equations, before returning to the full auxiliary scheme. -/
abbrev NormalizedSliceRing := AuxiliarySectionRing ⧸ normalizedSliceIdeal

/-- The original auxiliary coefficient functions descend to the normalization quotient. -/
def normalizedSliceQuotient : AuxiliarySectionRing →+* NormalizedSliceRing :=
  Ideal.Quotient.mk normalizedSliceIdeal

variable {R : Type} [CommRing R]

/-- A map on the original auxiliary functions satisfies the four normalization equations. -/
def SatisfiesNormalization (g : AuxiliarySectionRing →+* R) : Prop :=
  ∀ i, g (normalizedSliceRelation i) = 0

/-- Vanishing of the four functions is exactly vanishing of their generated ideal. -/
theorem satisfiesNormalization_iff (g : AuxiliarySectionRing →+* R) :
    SatisfiesNormalization g ↔ normalizedSliceIdeal ≤ RingHom.ker g := by
  rw [normalizedSliceIdeal, Ideal.span_le]
  constructor
  · intro h a ha
    obtain ⟨i, rfl⟩ := ha
    exact h i
  · intro h i
    exact h ⟨i, rfl⟩

/-- The quotient itself satisfies every original normalization equation. -/
theorem normalizedSliceQuotient_satisfies : SatisfiesNormalization normalizedSliceQuotient := by
  intro i
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

/-- Descend a coefficient map satisfying the actual normalization equations. -/
def normalizedSliceLift (g : AuxiliarySectionRing →+* R) (h : SatisfiesNormalization g) :
    NormalizedSliceRing →+* R :=
  Ideal.Quotient.lift normalizedSliceIdeal g (fun _ ha => (satisfiesNormalization_iff g).mp h ha)

/-- Descending retains the entire original coefficient map. -/
theorem normalizedSliceLift_comp (g : AuxiliarySectionRing →+* R)
    (h : SatisfiesNormalization g) :
    (normalizedSliceLift g h).comp normalizedSliceQuotient = g := rfl

/-- Quotient maps correspond exactly to maps satisfying the four frame equations. -/
def normalizedSliceRingRepresentation :
    (NormalizedSliceRing →+* R) ≃
      {g : AuxiliarySectionRing →+* R // SatisfiesNormalization g} where
  toFun f := ⟨f.comp normalizedSliceQuotient, fun i => by
    simp only [RingHom.comp_apply, normalizedSliceQuotient_satisfies i, map_zero]⟩
  invFun g := normalizedSliceLift g.val g.property
  left_inv f := Ideal.Quotient.ringHom_ext rfl
  right_inv g := Subtype.ext rfl

/-- The representing bijection commutes with every coefficient-ring extension. -/
theorem normalizedSliceRingRepresentation_natural {S : Type} [CommRing S]
    (f : R →+* S) (g : NormalizedSliceRing →+* R) :
    (normalizedSliceRingRepresentation (f.comp g)).val =
      f.comp (normalizedSliceRingRepresentation g).val := rfl

end FLT.Mazur.UniversalWeierstrass
