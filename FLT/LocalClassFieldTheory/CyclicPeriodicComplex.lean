/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The two-periodic cyclic complex

The Boolean index records parity, including the differential from odd back
to even degree. Its homologies are the actual norm/difference quotients.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory Rep Rep.FiniteCyclicGroup

/-- The two-cycle, with both differentials retained. -/
def cyclicPeriodicShape : ComplexShape Bool where
  Rel i j := Bool.not i = j
  next_eq h h' := h.symm.trans h'
  prev_eq h h' := by simpa using congrArg Bool.not (h.trans h'.symm)

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]

/-- Difference in even degree and norm in odd degree form a two-periodic complex. -/
def cyclicPeriodicComplex (A : Rep k G) (g : G) :
    HomologicalComplex (ModuleCat k) cyclicPeriodicShape where
  X _ := ModuleCat.of k A.V
  d i j := match i, j with
    | false, true => (subCompNormHom A g).f
    | true, false => (normHomCompSub A g).f
    | _, _ => 0
  shape := by intro i j h; cases i <;> cases j <;> simp_all [cyclicPeriodicShape]
  d_comp_d' := by
    intro i j l hij hjl
    cases i <;> cases j <;> cases l <;>
      simp_all only [cyclicPeriodicShape, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, Bool.true_eq_false]
    · exact (subCompNormHom A g).zero
    · exact (normHomCompSub A g).zero

/-- Equivariant coefficient maps act on the periodic complex in each degree. -/
def cyclicPeriodicMap {A B : Rep k G} (f : A ⟶ B) (g : G) :
    cyclicPeriodicComplex A g ⟶ cyclicPeriodicComplex B g where
  f _ := ModuleCat.ofHom f.hom.toLinearMap
  comm' := by
    intro i j hij
    cases i <;> cases j <;> simp_all only [cyclicPeriodicShape, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, Bool.true_eq_false]
    · have h : f ≫ (applyAsHom B g - 𝟙 B) = (applyAsHom A g - 𝟙 A) ≫ f := by
        simpa only [Preadditive.sub_comp, Preadditive.comp_sub,
          Category.id_comp, Category.comp_id] using
          congrArg (fun h => h - f) (applyAsHom_comm f g).symm
      exact congrArg (fun h : A ⟶ B => ModuleCat.ofHom h.hom.toLinearMap) h
    · exact congrArg (fun h : A ⟶ B => ModuleCat.ofHom h.hom.toLinearMap) (norm_comm f)

/-- The periodic complex construction is functorial in the coefficient representation. -/
def cyclicPeriodicFunctor (g : G) :
    Rep k G ⥤ HomologicalComplex (ModuleCat k) cyclicPeriodicShape where
  obj A := cyclicPeriodicComplex A g
  map f := cyclicPeriodicMap f g

instance cyclicPeriodicFunctor_additive (g : G) : (cyclicPeriodicFunctor (k := k) g).Additive where
  map_add := by intros; ext; rfl

end LocalClassFieldTheory
