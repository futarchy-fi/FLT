/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartStalkScalars
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Stalk neighborhoods at specified points

Actual scheme stalk maps at equal specified points descend to maximal-ideal
power quotients. These maps retain germs and composition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ClosedPointStalkMap

set_option backward.isDefEq.respectTransparency false

/-- The actual stalk map, with its image point identified with the specified point. -/
def pointMap {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y) (hy : f x = y) :
    Y.presheaf.stalk y ⟶ X.presheaf.stalk x := by
  subst y
  exact f.stalkMap x

instance pointMap_isLocalHom {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y)
    (hy : f x = y) : IsLocalHom (pointMap f x y hy).hom := by
  subst y
  change IsLocalHom (f.stalkMap x).hom
  infer_instance

/-- Specifying the image point does not change the map on germs of sections. -/
theorem pointMap_germ {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y) (hy : f x = y)
    (V : Y.Opens) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U) (hv : y ∈ V)
    (s : Γ(Y, V)) :
    pointMap f x y hy (Y.presheaf.germ V y hv s) =
      X.presheaf.germ U x hx (f.appLE V U hU s) := by
  subst y
  exact (AffineChartStalkScalars.germ_appLE f V U hU x hx s).symm

/-- Specified-point stalk maps retain composition of the actual scheme morphisms. -/
theorem pointMap_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z) (hy : f x = y) (hz : g y = z) :
    pointMap g y z hz ≫ pointMap f x y hy =
      pointMap (f ≫ g) x z (by rw [Scheme.Hom.comp_apply, hy, hz]) := by
  subst y
  subst z
  exact (Scheme.Hom.stalkMap_comp f g x).symm

/-- Equal scheme maps induce equal maps between the same specified stalks. -/
theorem pointMap_congr {X Y : Scheme} {f g : X ⟶ Y} (hfg : f = g)
    (x : X) (y : Y) (hf : f x = y) (hg : g x = y) :
    pointMap f x y hf = pointMap g x y hg := by
  subst g
  rfl

/-- The actual spectrum stalk map retains the given homomorphism on ring elements. -/
theorem pointMap_spec {A B : CommRingCat} (φ : B ⟶ A)
    (x : Spec A) (y : Spec B) (hy : Spec.map φ x = y) (b : B) :
    pointMap (Spec.map φ) x y hy (StructureSheaf.toStalk B y b) =
      StructureSheaf.toStalk A x (φ b) := by
  subst y
  convert AffineChartStalkScalars.chart_scalar (Spec.map φ) (𝟙 _) φ
    (Category.comp_id _) ⊤ x trivial b using 1
  rfl

/-- Actual stalk maps descend to any decreasing pair of maximal-ideal powers. -/
def quotientMap {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y) (hy : f x = y)
    {r s : ℕ} (hrs : r ≤ s) :
    (Y.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ s) →+*
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r) :=
  Ideal.quotientMap _ (pointMap f x y hy).hom (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact (pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le _) s).trans
      (Ideal.pow_le_pow_right hrs))

/-- Quotient stalk transitions retain the actual stalk map on representatives. -/
@[simp] theorem quotientMap_mk {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Y)
    (hy : f x = y) {r s : ℕ} (hrs : r ≤ s) (a : Y.presheaf.stalk y) :
    quotientMap f x y hy hrs (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (pointMap f x y hy a) := rfl

end FLT.Mazur.ClosedPointStalkMap
