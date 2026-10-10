/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFiberNeighborhood
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness near a fiber of a proper family

For a morphism over a base, quasi-finiteness along one whole base fiber
spreads to finiteness over a base neighborhood. Properness closes the bad
locus; Zariski's main theorem supplies finiteness on the remaining locus.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.Approximation

/-- Quasi-finiteness along a base fiber makes a proper map finite near that fiber. -/
theorem exists_finite_over_base_neighborhood {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [IsProper (f ≫ g)] [IsSeparated g] (s : S)
    (hf : ∀ x : (f ≫ g).fiber s, f.QuasiFiniteAt ((f ≫ g).fiberι s x)) :
    ∃ V : S.Opens, s ∈ V ∧ IsFinite (f ∣_ (g ⁻¹ᵁ V)) := by
  let _ : IsProper f := IsProper.of_comp f g
  obtain ⟨V, hsV, hV⟩ := exists_proper_fiber_neighborhood (f ≫ g) s f.quasiFiniteLocus
    (by rintro _ ⟨x, rfl⟩; exact hf x)
  refine ⟨V, hsV, ?_⟩
  have hq : LocallyQuasiFinite (f ∣_ (g ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    apply top_unique
    intro x _
    have hx : f.QuasiFiniteAt ((f ⁻¹ᵁ (g ⁻¹ᵁ V)).ι x) := hV x.2
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion,
      ← morphismRestrict_ι, Scheme.Hom.quasiFiniteAt_comp_iff] at hx
    exact hx
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end FLT.Mazur.Approximation
