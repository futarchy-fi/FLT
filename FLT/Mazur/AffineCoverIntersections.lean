/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Affine intersections and cohomology of restricted modules

On a separated scheme, each nonempty finite intersection of affine opens is
again affine. In particular this applies to every tuple intersection in the
Cech complex, including tuples with repeated entries. Restricting a
quasi-coherent module to these open subschemes gives zero cohomology in every
positive degree. Neither the size of the ambient family nor Noetherian
hypotheses enter this local statement.

These are cohomology groups on the open subschemes. Identifying them with the
ambient cohomology presheaf is a separate comparison needed to apply the
acyclic-cover theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

/-- A quasi-coherent module restricted to an affine open has no positive cohomology. -/
theorem affineOpen_moduleH_succ_subsingleton (W : X.Opens) (hW : IsAffineOpen W)
    (q : ℕ) : Subsingleton (ModuleH (M.restrict W.ι) (q + 1)) := by
  let affineOpenIsAffine : IsAffine W.toScheme := hW
  exact affine_moduleH_succ_subsingleton (M.restrict W.ι) q

/-- Vanishing on an affine open, expressed at an arbitrary positive degree. -/
theorem affineOpen_moduleH_eq_zero (W : X.Opens) (hW : IsAffineOpen W)
    (n : ℕ) (hn : 0 < n) (x : ModuleH (M.restrict W.ι) n) : x = 0 := by
  let affineOpenIsAffine : IsAffine W.toScheme := hW
  exact affine_moduleH_eq_zero (M.restrict W.ι) n hn x

variable [X.IsSeparated] {ι : Type u} (U : ι → X.Opens)

/-- Every tuple intersection of affine opens on a separated scheme is affine. -/
theorem affineCover_intersection_isAffineOpen (hU : ∀ i, IsAffineOpen (U i))
    (n : ℕ) (a : Fin (n + 1) → ι) : IsAffineOpen (CechSheafHZero.V U n a) :=
  IsAffineOpen.iInf fun j ↦ hU (a j)

/-- The restriction to any Cech tuple intersection has zero positive cohomology. -/
theorem affineCover_intersection_moduleH_succ_subsingleton
    (hU : ∀ i, IsAffineOpen (U i)) (n q : ℕ) (a : Fin (n + 1) → ι) :
    Subsingleton
      (ModuleH (M.restrict (Scheme.Opens.ι (CechSheafHZero.V U n a))) (q + 1)) :=
  affineOpen_moduleH_succ_subsingleton M _ (affineCover_intersection_isAffineOpen U hU n a) q

/-- Every positive-degree class on a Cech tuple intersection vanishes. -/
theorem affineCover_intersection_moduleH_eq_zero (hU : ∀ i, IsAffineOpen (U i))
    (n q : ℕ) (hq : 0 < q) (a : Fin (n + 1) → ι)
    (x : ModuleH (M.restrict (Scheme.Opens.ι (CechSheafHZero.V U n a))) q) : x = 0 :=
  affineOpen_moduleH_eq_zero M _ (affineCover_intersection_isAffineOpen U hU n a) q hq x

/-- A nonempty finite subfamily also has an affine intersection. -/
theorem affineCover_finset_intersection_isAffineOpen (hU : ∀ i, IsAffineOpen (U i))
    (s : Finset ι) (hs : s.Nonempty) : IsAffineOpen (⨅ i ∈ s, U i) :=
  IsAffineOpen.biInf (s : Set ι) s.finite_toSet hs (fun i _ ↦ hU i)

/-- Positive cohomology vanishes after restriction to a nonempty finite subfamily. -/
theorem affineCover_finset_intersection_moduleH_succ_subsingleton
    (hU : ∀ i, IsAffineOpen (U i)) (s : Finset ι) (hs : s.Nonempty) (q : ℕ) :
    Subsingleton (ModuleH (M.restrict (⨅ i ∈ s, U i).ι) (q + 1)) :=
  affineOpen_moduleH_succ_subsingleton M _
    (affineCover_finset_intersection_isAffineOpen U hU s hs) q

end FLT.Mazur.FCurve
