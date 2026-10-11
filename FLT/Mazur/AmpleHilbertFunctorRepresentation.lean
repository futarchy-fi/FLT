/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAmbientHilbertClassification
public import Mathlib.CategoryTheory.Yoneda

/-!
# Natural representation of full finite flat families

The constructed Hilbert scheme represents full ideal families on all test
schemes of a proper ample ambient. The natural equivalence uses the original
universal ideal and arbitrary base change, including nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open FLT.Mazur.ClosedIdealCover FLT.Mazur.FCurve
namespace FLT.Mazur.HilbertChart
variable {R : Type} [CommRing R] {Z : Scheme} (z : Z ⟶ Spec (.of R))

/-- Full degree-d ideal families, with their actual arbitrary ideal pullbacks. -/
def relativeIdealFamilyPresheaf (d : ℕ) : (Over (Spec (.of R)))ᵒᵖ ⥤ Type where
  obj T := RelativeIdealFamilies z d T.unop.hom
  map g := ↾(relativeIdealFamilyBaseChange z d _ _ g.unop.left (Over.w g.unop))
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro J
    exact relativeIdealFamilyBaseChange_id z d T.unop.hom J
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro J
    exact (relativeIdealFamilyBaseChange_comp z d _ _ _ _ _ _ _ J).symm

/-- The existing parameter scheme with its original structure morphism. -/
def ampleHilbertTest (d : ℕ) : Over (Spec (.of R)) :=
  Over.mk ((allAffineAmbientCharts z).gluedBase d)

/-- Actual relative morphisms are the existing glued Hilbert parameters. -/
def ampleHilbertParameterEquiv (d : ℕ) (T : Over (Spec (.of R))) :
    (T ⟶ ampleHilbertTest z d) ≃ (allAffineAmbientCharts z).GluedParameters d T.hom where
  toFun k := ⟨k.left, Over.w k⟩
  invFun p := Over.homMk p.val p.property
  left_inv k := by apply Over.OverMorphism.ext; rfl
  right_inv p := rfl

variable [IsProper z] {L : Z.Modules} (hL : AmpleLineBundle L)

/-- The full universal family gives the classifying equivalence on each original test. -/
def ampleHilbertFamilyEquiv (d : ℕ) (T : Over (Spec (.of R))) :
    (T ⟶ ampleHilbertTest z d) ≃ RelativeIdealFamilies z d T.hom :=
  (ampleHilbertParameterEquiv z d T).trans (ampleAmbientClassification z hL d T.hom)

/-- The actual Hilbert scheme represents the full finite flat family presheaf. -/
def ampleHilbertFamilyIso (d : ℕ) :
    yoneda.obj (ampleHilbertTest z d) ≅ relativeIdealFamilyPresheaf z d :=
  NatIso.ofComponents (fun T ↦ (ampleHilbertFamilyEquiv z hL d T.unop).toIso)
    (fun {T U} g ↦ by
      apply ConcreteCategory.hom_ext
      intro k
      exact ((allAffineAmbientCharts z).parameterFamily_natural d T.unop.hom U.unop.hom
        g.unop.left (Over.w g.unop) (ampleHilbertParameterEquiv z d T.unop k)).symm)

/-- Classification pulls back the entire universal ideal along the actual ambient map. -/
lemma ampleHilbertFamilyIso_ideal (d : ℕ) (T : Over (Spec (.of R)))
    (k : T ⟶ ampleHilbertTest z d) :
    ((ampleHilbertFamilyIso z hL d).hom.app (op T) k).val =
      ((allAffineAmbientCharts z).universalIdeal d).comap
        (relativeIdealAmbientMap z ((allAffineAmbientCharts z).gluedBase d)
          T.hom k.left (Over.w k)) := rfl

end FLT.Mazur.HilbertChart
