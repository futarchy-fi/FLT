/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSortingHomotopyEvaluation
public import Mathlib.Algebra.Homology.Homotopy

/-!
# The sorting homotopy equivalence

The integral coordinate homotopy makes restriction to increasing tuples a
homotopy equivalence, and hence an equivalence on cohomology in every degree.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace FLT.Mazur.CechSortingHomotopy

open CechSheafHZero CechSortingMaps CechSortingHomotopyEvaluation

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]
variable (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- The coordinate homotopy transported to the actual Cech terms. -/
def component (n : ℕ) : (C U F).X (n + 1) ⟶ (C U F).X n :=
  AddCommGrpCat.ofHom ((termEquiv U F n).symm.toAddMonoidHom.comp
    ((homotopyCoordinate U F n).comp (termEquiv U F (n + 1)).toAddMonoidHom))

lemma component_apply (n : ℕ) (x : (C U F).X (n + 1)) :
    termEquiv U F n (component U F n x) =
      homotopyCoordinate U F n (termEquiv U F (n + 1) x) :=
  (termEquiv U F n).apply_symm_apply _

/-- The degree-lowering components, indexed by the complex shape. -/
def shapeComponent (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    (C U F).X i ⟶ (C U F).X j := by
  obtain rfl : j + 1 = i := h
  exact component U F j

/-- The null-homotopic map is precisely the defect of signed sorting. -/
lemma nullHomotopicMap_eq : Homotopy.nullHomotopicMap' (shapeComponent U F) =
    𝟙 (C U F) - restriction U F ≫ sorting U F := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl) (by intro l; simp)]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply (termEquiv U F 0).injective
    change termEquiv U F 0 (component U F 0 ((C U F).d 0 1 x)) =
      termEquiv U F 0 (x - (sorting U F).f 0 ((restriction U F).f 0 x))
    rw [component_apply, map_sub, ← fullD_eq]
    change _ = termEquiv U F 0 x - termEquiv U F 0
      ((termEquiv U F 0).symm (sortingHom U F 0
        (IncreasingCechComplex.restrict U F 0 (termEquiv U F 0 x))))
    rw [AddEquiv.apply_symm_apply]
    exact homotopyCoordinate_equation_zero U F (termEquiv U F 0 x)
  | succ n =>
    rw [Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl)]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply (termEquiv U F (n + 1)).injective
    change termEquiv U F (n + 1)
      (component U F (n + 1) ((C U F).d (n + 1) (n + 1 + 1) x) +
        (C U F).d n (n + 1) (component U F n x)) =
      termEquiv U F (n + 1)
        (x - (sorting U F).f (n + 1) ((restriction U F).f (n + 1) x))
    rw [map_add, component_apply, ← fullD_eq, ← fullD_eq, component_apply, map_sub]
    change _ = termEquiv U F (n + 1) x - termEquiv U F (n + 1)
      ((termEquiv U F (n + 1)).symm (sortingHom U F (n + 1)
        (IncreasingCechComplex.restrict U F (n + 1) (termEquiv U F (n + 1) x))))
    rw [AddEquiv.apply_symm_apply]
    exact (add_comm _ _).trans
      (homotopyCoordinate_equation U F n (termEquiv U F (n + 1) x))

/-- Signed sorting after restriction is homotopic to the identity. -/
def sortingHomotopy : Homotopy (restriction U F ≫ sorting U F) (𝟙 (C U F)) := by
  have h := Homotopy.nullHomotopy' (shapeComponent U F)
  rw [nullHomotopicMap_eq] at h
  exact (Homotopy.equivSubZero.symm h).symm

/-- The full and increasing Cech complexes are homotopy equivalent. -/
def homotopyEquiv : HomotopyEquiv (C U F) (IncreasingCechComplex.complex U F) where
  hom := restriction U F
  inv := sorting U F
  homotopyHomInvId := sortingHomotopy U F
  homotopyInvHomId := Homotopy.ofEq (sorting_restriction U F)

/-- Restriction induces an isomorphism on homology in every degree. -/
def homologyIso (n : ℕ) : CH U F n ≅ (IncreasingCechComplex.complex U F).homology n :=
  (homotopyEquiv U F).toHomologyIso n

/-- The same comparison as an additive equivalence of cohomology groups. -/
def homologyEquiv (n : ℕ) :
    CH U F n ≃+ (IncreasingCechComplex.complex U F).homology n :=
  (homologyIso U F n).addCommGroupIsoToAddEquiv

/-- The homology comparison is natural in the coefficient sheaf. -/
lemma homologyIso_naturality {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) :
    CHmap U f n ≫ (homologyIso U G n).hom =
      (homologyIso U F n).hom ≫ HomologicalComplex.homologyMap (coefficientMap U f) n := by
  change HomologicalComplex.homologyMap _ n ≫
    HomologicalComplex.homologyMap (restriction U G) n =
      HomologicalComplex.homologyMap (restriction U F) n ≫
        HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    restriction_naturality]

end FLT.Mazur.CechSortingHomotopy
