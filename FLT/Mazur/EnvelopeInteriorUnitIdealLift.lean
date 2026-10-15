/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EnvelopeBoundaryIdealTransport

/-!
# Unit-ideal certificates lift whole affine tests to the original interior

The original denominator ideal becomes the unit ideal on an affine test
exactly when its entire map factors through the interior. Any generating
set gives the same test; no individual generator need be a global unit.
The factorization is unique as a scheme map and retains nilpotent structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {Y X Z : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens)
  [IsAffine X] [IsAffine Z] (a : Z ⟶ X)

/-- Unit-ideal generation is an exact whole-test certificate of interior membership. -/
theorem map_denominator_eq_top_iff :
    (denominatorIdeal π.appTop.hom O).map a.appTop.hom = ⊤ ↔
      Set.range a ⊆ fullFiberInterior π O := by
  rw [← affine_zeroLocus_empty_iff, zeroLocus_map_denominator]
  constructor
  · intro h x hx
    obtain ⟨z, rfl⟩ := hx
    by_contra hn
    have hz : z ∈ (a ⁻¹' (fullFiberInterior π O : Set X))ᶜ := hn
    rw [h] at hz
    exact hz
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz (h ⟨z, rfl⟩)

/-- Finite or infinite generators test the whole morphism by one ideal equality. -/
theorem generator_span_eq_top_iff (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = denominatorIdeal π.appTop.hom O) :
    Ideal.span (a.appTop.hom '' s) = ⊤ ↔ Set.range a ⊆ fullFiberInterior π O := by
  rw [← Ideal.map_span, hs, map_denominator_eq_top_iff]

variable (h : (denominatorIdeal π.appTop.hom O).map a.appTop.hom = ⊤)

/-- The certificate constructs an actual whole scheme lift. -/
def unitIdealInteriorLift : Z ⟶ (fullFiberInterior π O).toScheme :=
  IsOpenImmersion.lift (fullFiberInterior π O).ι a (by
    rw [Scheme.Opens.range_ι]
    exact (map_denominator_eq_top_iff π O a).mp h)

/-- The lift preserves the entire original map. -/
@[reassoc]
theorem unitIdealInteriorLift_comp :
    unitIdealInteriorLift π O a h ≫ (fullFiberInterior π O).ι = a :=
  IsOpenImmersion.lift_fac _ _ _

/-- The certificate permits only one scheme factorization, also on nonreduced tests. -/
theorem unitIdealInteriorLift_unique (b : Z ⟶ (fullFiberInterior π O).toScheme)
    (hb : b ≫ (fullFiberInterior π O).ι = a) : b = unitIdealInteriorLift π O a h := by
  apply (cancel_mono (fullFiberInterior π O).ι).mp
  exact hb.trans (unitIdealInteriorLift_comp π O a h).symm

end FLT.Mazur.SchemeOpenEnvelope
