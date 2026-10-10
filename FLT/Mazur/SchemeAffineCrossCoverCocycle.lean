/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossCoverDescent
public import FLT.Mazur.SchemeDescentPairTransport

/-!
# Cocycle for effective affine cross-cover comparisons

Three independent covering maps over one affine base give effective
comparisons whose composite is the direct comparison. Faithful reconstruction
reduces the equality to the cocycle of the original scheme descent transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data

private theorem reconstruction_comp {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {a b c : A} {x y z : B} (f : a ⟶ b) (g : b ⟶ c)
    (r : F.obj a ⟶ x) (s : F.obj b ⟶ y) (t : F.obj c ⟶ z)
    (v : x ⟶ y) (w : y ⟶ z) (q : x ⟶ z)
    (hf : F.map f ≫ s = r ≫ v) (hg : F.map g ≫ t = s ≫ w)
    (hvw : v ≫ w = q) : F.map (f ≫ g) ≫ t = r ≫ q := by
  rw [Functor.map_comp, Category.assoc, hg, ← Category.assoc, hf,
    Category.assoc, hvw]

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)
variable (a : Spec R ⟶ X) (b c d : Spec S ⟶ Y)
variable (wb : Spec.map φ ≫ a = b ≫ p) (wc : Spec.map φ ≫ a = c ≫ p)
variable (wd : Spec.map φ ≫ a = d ≫ p) (hφ : φ.hom.FaithfullyFlat)
variable [((pullback b).obj M).IsQuasicoherent]
variable [((pullback c).obj M).IsQuasicoherent]
variable [((pullback d).obj M).IsQuasicoherent]
attribute [local irreducible] chartSheaf chartReconstruction chartCrossCoverIso

/-- Effective affine comparisons retain the original descent transport cocycle. -/
theorem chartCrossCoverIso_cocycle :
    (D.chartCrossCoverIso φ p a b c wb wc hφ).hom ≫
        (D.chartCrossCoverIso φ p a c d wc wd hφ).hom =
      (D.chartCrossCoverIso φ p a b d wb wd hφ).hom := by
  apply D.chartCrossCoverIso_unique φ p a b d wb wd hφ
  exact reconstruction_comp (pullback (Spec.map φ))
    (D.chartCrossCoverIso φ p a b c wb wc hφ).hom
    (D.chartCrossCoverIso φ p a c d wc wd hφ).hom
    (D.chartReconstruction φ p a b wb hφ).hom
    (D.chartReconstruction φ p a c wc hφ).hom
    (D.chartReconstruction φ p a d wd hφ).hom
    (D.transport b c (wb.symm.trans wc)).hom
    (D.transport c d (wc.symm.trans wd)).hom
    (D.transport b d (wb.symm.trans wd)).hom
    (D.chartCrossCoverIso_reconstruction φ p a b c wb wc hφ)
    (D.chartCrossCoverIso_reconstruction φ p a c d wc wd hφ)
    (D.transport_comp b c d (wb.symm.trans wc) (wc.symm.trans wd))

/-- The cocycle also holds as an equality of the effective isomorphisms. -/
theorem chartCrossCoverIso_trans :
    D.chartCrossCoverIso φ p a b c wb wc hφ ≪≫
        D.chartCrossCoverIso φ p a c d wc wd hφ =
      D.chartCrossCoverIso φ p a b d wb wd hφ := by
  apply Iso.ext
  exact D.chartCrossCoverIso_cocycle φ p a b c d wb wc wd hφ

end FLT.Mazur.SchemeGeometricDescent.Data
