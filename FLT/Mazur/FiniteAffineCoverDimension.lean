/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoverCohomology
public import FLT.Mazur.CechSortingHomotopy

/-!
# Cohomological dimension from a specified finite affine cover

For a quasi-coherent module on a separated scheme, a cover by `r` affine opens
gives vanishing of actual module cohomology in degrees at least `r`. The cover
is supplied explicitly, so no quasi-compactness assumption is needed. The empty
cover gives vanishing in every degree, including degree zero.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.IncreasingCechComplex

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι] [Fintype ι]
variable (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Homology vanishes wherever the increasing Cech term vanishes. -/
lemma homology_isZero (n : ℕ) (h : Fintype.card ι ≤ n) :
    IsZero ((complex U F).homology n) :=
  ((complex U F).sc n).isZero_homology_of_isZero_X₂ (complex_isZero U F n h)

end FLT.Mazur.IncreasingCechComplex

namespace FLT.Mazur.CechSortingHomotopy

variable {X : TopCat.{u}} {ι : Type u} [Fintype ι]
variable (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- A finite cover's full Cech cohomology vanishes at the cardinal bound. -/
lemma finiteCover_cohomology_subsingleton (n : ℕ) (h : Fintype.card ι ≤ n) :
    Subsingleton (CechSheafHZero.CH U F n) := by
  let _indexOrder : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact AddCommGrpCat.subsingleton_of_isZero
    ((IncreasingCechComplex.homology_isZero U F n h).of_iso (homologyIso U F n))

end FLT.Mazur.CechSortingHomotopy

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} [X.IsSeparated] {ι : Type u}
variable (M : X.Modules) [M.IsQuasicoherent] (U : ι → X.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include hU hCover

/-- The specified finite affine cover bounds actual module cohomology. -/
theorem finiteAffineCover_moduleH_subsingleton [Fintype ι] (n : ℕ)
    (h : Fintype.card ι ≤ n) : Subsingleton (ModuleH M n) := by
  let _cechSubsingleton :=
    CechSortingHomotopy.finiteCover_cohomology_subsingleton U (moduleAbelianSheaf M) n h
  exact (affineCoverCechEquiv M U hU hCover n).symm.toEquiv.injective.subsingleton

/-- Every cohomology class vanishes from the number of affine charts onwards. -/
theorem finiteAffineCover_moduleH_eq_zero [Fintype ι] (n : ℕ)
    (h : Fintype.card ι ≤ n) (x : ModuleH M n) : x = 0 := by
  let _moduleHSubsingleton := finiteAffineCover_moduleH_subsingleton M U hU hCover n h
  exact Subsingleton.elim _ _

/-- An empty affine cover forces cohomology to vanish even in degree zero. -/
theorem emptyAffineCover_moduleH_subsingleton [IsEmpty ι] (n : ℕ) :
    Subsingleton (ModuleH M n) := by
  let _emptyIndexFintype : Fintype ι := Fintype.ofIsEmpty
  exact finiteAffineCover_moduleH_subsingleton M U hU hCover n (by simp)

/-- With an empty cover, every actual module cohomology class is zero. -/
theorem emptyAffineCover_moduleH_eq_zero [IsEmpty ι] (n : ℕ) (x : ModuleH M n) :
    x = 0 := by
  let _moduleHSubsingleton := emptyAffineCover_moduleH_subsingleton M U hU hCover n
  exact Subsingleton.elim _ _

end FLT.Mazur.FCurve
