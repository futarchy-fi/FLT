/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeProperGeometricFiberSections
public import FLT.Mazur.CurveGenus

/-!
# Geometric fiber comparisons with actual degree-zero cohomology

The geometric global-functions theorem supplies the constants map to
actual cohomology. Its section-level comparisons commute with field maps
and scheme maps over them, retaining the original scalar pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeProperGeometricFiberSections
variable {K L : Type u} [Field K] [Field L] {X Y S : Scheme.{u}}

/-- The actual scalar maps commute with any square over a map of base fields. -/
lemma scalarMap_naturality (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of L))
    (a : Y ⟶ X) (b : CommRingCat.of K ⟶ CommRingCat.of L)
    (w : a ≫ f = g ≫ Spec.map b) :
    scalarMap f ≫ a.appTop = b ≫ scalarMap g := by
  dsimp only [scalarMap]
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, w, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- The constructed global-function isomorphisms commute with actual field squares. -/
lemma sectionsIso_naturality [IsAlgClosed K] [IsAlgClosed L]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of L))
    [IsIntegral X] [IsIntegral Y] [UniversallyClosed f] [UniversallyClosed g]
    (a : Y ⟶ X) (b : CommRingCat.of K ⟶ CommRingCat.of L)
    (w : a ≫ f = g ≫ Spec.map b) :
    (sectionsIso f).hom ≫ a.appTop = b ≫ (sectionsIso g).hom :=
  scalarMap_naturality f g a b w

variable (f : X ⟶ S) [UniversallyClosed f] [GeometricallyIntegral f] [IsAlgClosed K]

/-- Geometric fibers satisfy the existing constant-global-sections predicate. -/
lemma geometricFiber_constantSections (a : Spec (.of K) ⟶ S) :
    FCurve.HasConstantGlobalSections (Limits.pullback.snd f a) := by
  let _ := GeometricallyIntegral.isIntegral_of_subsingleton (Limits.pullback.snd f a)
  exact scalarMap_bijective (Limits.pullback.snd f a)

/-- The actual constants map identifies the field with geometric fiber H0. -/
def geometricFiberH0Equiv (a : Spec (.of K) ⟶ S) :
    K ≃ₗ[K] FCurve.H0 (Limits.pullback.snd f a) :=
  FCurve.scalarH0ConstantsEquiv _ (geometricFiber_constantSections f a)

/-- The cohomology equivalence retains the original constants map. -/
lemma geometricFiberH0Equiv_apply (a : Spec (.of K) ⟶ S) (r : K) :
    geometricFiberH0Equiv f a r = FCurve.scalarH0Constants (Limits.pullback.snd f a) r := rfl

/-- Actual degree-zero cohomology of each geometric fiber has dimension one. -/
lemma geometricFiber_finrank_H0 (a : Spec (.of K) ⟶ S) :
    Module.finrank K (FCurve.H0 (Limits.pullback.snd f a)) = 1 :=
  FCurve.finrank_H0_of_constantGlobalSections _ (geometricFiber_constantSections f a)

end FLT.Mazur.SchemeProperGeometricFiberSections
