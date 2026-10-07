/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeGeometricDescentCocycleTest
public import FLT.Mazur.SchemeOverlapNormalizationNaturality

/-!
# Descent transport between two maps with the same base image

The original overlap constructs transport between arbitrary maps into the
cover over the same base map. Its cocycle proves composition, units, and
inverses, and transport commutes with further pullback and compatible maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules} (D : Data p M)

/-- Transport along the actual pair of maps, using their equality only over the base. -/
def transport (b c : T ⟶ Y) (w : b ≫ p = c ≫ p) :
    (pullback b).obj M ≅ (pullback c).obj M :=
  normalize (Limits.pullback.fst p p) (Limits.pullback.snd p p)
    (Limits.pullback.lift b c w) b c (Limits.pullback.lift_fst _ _ _)
      (Limits.pullback.lift_snd _ _ _) M D.overlap

/-- Transport along three compatible maps satisfies the original cocycle. -/
@[reassoc]
theorem transport_comp (a b c : T ⟶ Y) (wab : a ≫ p = b ≫ p)
    (wbc : b ≫ p = c ≫ p) :
    (D.transport a b wab).hom ≫ (D.transport b c wbc).hom =
      (D.transport a c (wab.trans wbc)).hom :=
  D.cocycle_on_pairs p (Limits.pullback.lift a b wab) (Limits.pullback.lift b c wbc)
    (Limits.pullback.lift a c (wab.trans wbc)) a b c
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)

/-- Transport from a map to itself is the identity. -/
@[simp]
theorem transport_self (b : T ⟶ Y) : D.transport b b rfl = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_mono (D.transport b b rfl).hom).mp
  simpa only [Category.id_comp, Iso.refl_hom] using D.transport_comp b b b rfl rfl

/-- Reversing the two maps gives the inverse transport. -/
theorem transport_symm (b c : T ⟶ Y) (w : b ≫ p = c ≫ p) :
    D.transport c b w.symm = (D.transport b c w).symm := by
  apply Iso.ext
  apply (cancel_epi (D.transport b c w).hom).mp
  rw [D.transport_comp, D.transport_self, Iso.refl_hom, Iso.symm_hom, Iso.hom_inv_id]

/-- Transport commutes with restriction to a further test scheme. -/
theorem transport_pullback {T' : Scheme.{u}} (b c : T ⟶ Y)
    (w : b ≫ p = c ≫ p) (t : T' ⟶ T) (b' c' : T' ⟶ Y)
    (hb : t ≫ b = b') (hc : t ≫ c = c') (w' : b' ≫ p = c' ≫ p) :
    normalize b c t b' c' hb hc M (D.transport b c w) = D.transport b' c' w' := by
  apply normalize_comp_of_eq (Limits.pullback.fst p p) (Limits.pullback.snd p p)
    (Limits.pullback.lift b c w) b c _ _ t (Limits.pullback.lift b' c' w')
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Limits.pullback.lift_fst, hb]
  · simp only [Category.assoc, Limits.pullback.lift_snd, hc]

/-- Transport is natural in every morphism compatible with the original overlap. -/
@[reassoc]
theorem transport_naturality {N : Y.Modules} (E : Data p N) (f : M ⟶ N)
    (hf : D.MapCompatible p E f) (b c : T ⟶ Y) (w : b ≫ p = c ≫ p) :
    (D.transport b c w).hom ≫ (pullback c).map f =
      (pullback b).map f ≫ (E.transport b c w).hom :=
  normalize_compatible (Limits.pullback.fst p p) (Limits.pullback.snd p p)
    (Limits.pullback.lift b c w) b c _ _ D.overlap E.overlap f hf

end FLT.Mazur.SchemeGeometricDescent.Data
