/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# A concrete coefficient sequence for dimension shifting

Embed a representation in functions on the group with right translation action.
The cokernel is a genuine quotient representation, and the sequence is short exact.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)

/-- Functions with right translation action, the coinduced coefficient module. -/
def coinducedCoefficients : Rep k G := Rep.of {
  toFun g := LinearMap.funLeft k M (fun x : G => x * g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc] }

/-- The orbit function embeds the original representation. -/
def coinducedInclusion : M ⟶ coinducedCoefficients M := Rep.ofHom
  ⟨LinearMap.pi fun g => M.ρ g, fun g => by
    ext m x
    change M.ρ x (M.ρ g m) = M.ρ (x * g) m
    simp⟩

/-- Evaluation at the identity is a left inverse to the orbit embedding. -/
theorem coinducedInclusion_injective : Function.Injective (coinducedInclusion M).hom := by
  intro x y h
  have := congrFun h 1
  change M.ρ 1 x = M.ρ 1 y at this
  simpa using this

/-- The image of the orbit embedding is invariant under translation. -/
theorem coinducedInclusion_range_stable (g : G) :
    LinearMap.range (coinducedInclusion M).hom.toLinearMap ≤
      (LinearMap.range (coinducedInclusion M).hom.toLinearMap).comap
        ((coinducedCoefficients M).ρ g) := by
  rintro _ ⟨m, rfl⟩
  exact ⟨M.ρ g m, Rep.hom_comm_apply (coinducedInclusion M) g m⟩

/-- The coefficient module obtained by quotienting out the orbit functions. -/
abbrev shiftedCoefficients : Rep k G :=
  (coinducedCoefficients M).quotient
    (LinearMap.range (coinducedInclusion M).hom.toLinearMap)
    (coinducedInclusion_range_stable M)

/-- Projection onto the dimension-shift coefficient module. -/
def shiftedProjection : coinducedCoefficients M ⟶ shiftedCoefficients M :=
  (coinducedCoefficients M).mkQ
    (LinearMap.range (coinducedInclusion M).hom.toLinearMap)
    (coinducedInclusion_range_stable M)

/-- The concrete coefficient sequence used in the two-extension construction. -/
def coinducedCoefficientSequence : ShortComplex (Rep k G) :=
  ShortComplex.mk (coinducedInclusion M) (shiftedProjection M) (by
    ext m
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩)

/-- Orbit inclusion and quotient projection form a short exact sequence. -/
theorem coinducedCoefficientSequence_shortExact :
    (coinducedCoefficientSequence M).ShortExact where
  mono_f := (Rep.mono_iff_injective _).mpr (coinducedInclusion_injective M)
  epi_g := (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k))]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).mp hx

end LocalClassFieldTheory
