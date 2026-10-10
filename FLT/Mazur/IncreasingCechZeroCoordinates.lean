/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechZeroSections

/-!
# Coordinates of the actual global-section zero cycle

The bounded zero-cycle equivalence sends a section to its actual restrictions
on singleton intersections. This records the normalization of sheaf gluing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex CechSheafHZero FCurve Chow

variable {X : Scheme.{0}} {ι : Type} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens)

omit [LinearOrder ι] in
/-- Singleton coordinate reindexing is restriction along the singleton-open equality. -/
lemma zeroTermEquiv_coordinate (x : (C U (moduleAbelianSheaf M)).X 0)
    (a : Fin 1 → ι) :
    M.presheaf.map (eqToHom (congrArg op (singleOpen_eq U a)))
      (termEquiv U (moduleAbelianSheaf M) 0 x a) =
        zeroTermEquiv U (moduleAbelianSheaf M) x (a 0) := by
  have ha : a = fun _ ↦ a 0 := by ext i; congr 1; exact Subsingleton.elim _ _
  obtain ⟨i, rfl⟩ : ∃ i, a = fun _ ↦ i := ⟨a 0, ha⟩
  rw [zeroTermEquiv_apply, termEquiv_apply]
  change M.presheaf.map _ (M.presheaf.map _ _) = M.presheaf.map _ _
  rw [← Functor.map_comp_apply]
  rfl

variable {R : Type} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (hCover : iSup U = ⊤)

/-- Every bounded zero-cycle coordinate is the original section restricted to that open. -/
lemma baseSectionsZeroKernelEquiv_apply (s : baseSections M ρ ⊤)
    (a : Tuple (ι := ι) 0) :
    (baseSectionsZeroKernelEquiv M U ρ hCover s).val a =
      baseRestriction M ρ (show V U 0 a.val ≤ ⊤ from le_top) s := by
  let x := (fullZeroChartEquiv M U).symm
    (baseSectionsEqualizer M (RingHom.id _) U hCover s)
  change termEquiv U (moduleAbelianSheaf M) 0 x.val a.val = _
  apply (ConcreteCategory.bijective_of_isIso
    (M.presheaf.mapIso (eqToIso (congrArg op (singleOpen_eq U a.val)))).hom).injective
  change M.presheaf.map (eqToHom (congrArg op (singleOpen_eq U a.val)))
    (termEquiv U (moduleAbelianSheaf M) 0 x.val a.val) = _
  rw [zeroTermEquiv_coordinate]
  have hx := congrArg (fun z ↦ z.val (a.val 0)) ((fullZeroChartEquiv M U).apply_symm_apply
    (baseSectionsEqualizer M (RingHom.id _) U hCover s))
  change zeroTermEquiv U (moduleAbelianSheaf M) x.val (a.val 0) = _ at hx
  rw [hx]
  change M.presheaf.map _ s = M.presheaf.map _ (M.presheaf.map _ s)
  rw [← Functor.map_comp_apply]
  rfl

end FLT.Mazur.IncreasingCechScalars
