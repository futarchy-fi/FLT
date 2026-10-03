/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleExtensionChange
public import FLT.LocalClassFieldTheory.TateTwoExtension

/-!
# Descent of the Tate two-extension operation to H²

Changing a two-cocycle by a boundary changes its shifted one-cocycle by a
boundary. The extension comparison fixes both ends, so the Tate operation
depends only on the two-class, in every integer degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)

/-- Boundaries of two-cocycles give the explicit translation between shifted extensions. -/
theorem shiftedTwoCocycle_change (c c' : cocycles₂ M) (f : G → M)
    (hf : d₁₂ M f = ⇑c - ⇑c') (g : G) :
    shiftedTwoCocycle M c' g + (shiftedProjection M).hom f =
      (shiftedCoefficients M).ρ g ((shiftedProjection M).hom f) +
        shiftedTwoCocycle M c g := by
  change (shiftedProjection M).hom (twoCocyclePrimitive M c' g) + _ =
    _ + (shiftedProjection M).hom (twoCocyclePrimitive M c g)
  rw [← Rep.hom_comm_apply, ← map_add, ← map_add]
  let fI : coinducedCoefficients M := f
  have h : twoCocyclePrimitive M c' g + fI =
      (coinducedCoefficients M).ρ g fI + twoCocyclePrimitive M c g -
        (coinducedInclusion M).hom (f g) := by
    funext x
    have hx := congrFun hf (x, g)
    change M.ρ x (f g) - f (x * g) + f x = c (x, g) - c' (x, g) at hx
    change c' (x, g) + f x = f (x * g) + c (x, g) - M.ρ x (f g)
    rw [← (eq_sub_iff_add_eq).mp hx]
    abel
  rw [h, map_sub]
  have hz : (shiftedProjection M).hom ((coinducedInclusion M).hom (f g)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨f g, rfl⟩
  rw [hz, sub_zero]

variable [Fintype G]

/-- The operation is independent of the chosen representative of the two-class. -/
theorem tateTwoExtensionMap_eq_of_class_eq (c c' : cocycles₂ M)
    (h : H2π M c = H2π M c') (n : ℤ) :
    tateTwoExtensionMap M c n = tateTwoExtensionMap M c' n := by
  obtain ⟨f, hf⟩ := (H2π_eq_iff c c').mp h
  have hb := oneCocycle_tateConnecting_change (shiftedCoefficients M)
    (shiftedTwoCocycle M c') (shiftedTwoCocycle M c) ((shiftedProjection M).hom f)
    (shiftedTwoCocycle_change M c c' f hf) n
  exact congrArg (fun a => a ≫
    TateCohomology.δ (coinducedCoefficientSequence_shortExact M) (n + 1) ≫
      eqToHom (by congr 1; omega)) hb.symm

/-- Choose a representative of an actual two-class. -/
def twoClassRepresentative (a : groupCohomology M 2) : cocycles₂ M :=
  Classical.choose ((ModuleCat.epi_iff_surjective (H2π M)).mp inferInstance a)

omit [Fintype G] in
/-- The chosen cocycle represents exactly the supplied class. -/
theorem twoClassRepresentative_spec (a : groupCohomology M 2) :
    H2π M (twoClassRepresentative M a) = a :=
  Classical.choose_spec ((ModuleCat.epi_iff_surjective (H2π M)).mp inferInstance a)

/-- The two-extension action of a cohomology class on Tate cohomology. -/
def tateTwoClassMap (a : groupCohomology M 2) (n : ℤ) :
    tateCohomology (Rep.trivial k G k) n ⟶ tateCohomology M (n + 2) :=
  tateTwoExtensionMap M (twoClassRepresentative M a) n

/-- Every representative computes the same all-degree map. -/
theorem tateTwoClassMap_class (c : cocycles₂ M) (n : ℤ) :
    tateTwoClassMap M (H2π M c) n = tateTwoExtensionMap M c n :=
  tateTwoExtensionMap_eq_of_class_eq M _ c (twoClassRepresentative_spec M _) n

end LocalClassFieldTheory
