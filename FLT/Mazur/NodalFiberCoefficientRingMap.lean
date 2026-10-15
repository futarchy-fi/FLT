/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberCoefficientMap

/-!
# Specified ring homomorphisms on complete smoothing nodes

The node restriction retains the original coefficient homomorphism and both
labeled coordinates. Constants and these coordinates determine every ring map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (c : R) (d : S) (hc : f c = d)

/-- Change node coefficients using the specified original ring homomorphism. -/
def coefficientRingMap : Coordinate c →+* Coordinate d := by
  letI := f.toAlgebra
  exact (coefficientMap c d hc).toRingHom

/-- The first label survives the original ring restriction. -/
@[simp] theorem coefficientRingMap_p : coefficientRingMap f c d hc (p c) = p d := by
  let _ := f.toAlgebra
  exact coefficientMap_p c d hc

/-- The second label survives the original ring restriction. -/
@[simp] theorem coefficientRingMap_q : coefficientRingMap f c d hc (q c) = q d := by
  let _ := f.toAlgebra
  exact coefficientMap_q c d hc

/-- Every constant follows the specified original ring restriction. -/
@[simp] theorem coefficientRingMap_algebraMap (a : R) :
    coefficientRingMap f c d hc (algebraMap R (Coordinate c) a) =
      algebraMap S (Coordinate d) (f a) := by
  let _ := f.toAlgebra
  exact coefficientMap_scalar c d hc a

/-- Constants and the two labeled node coordinates determine the entire ring map. -/
theorem coefficient_ringHom_ext {T : Type*} [CommRing T]
    (g h : Coordinate c →+* T)
    (hc : ∀ a, g (algebraMap R _ a) = h (algebraMap R _ a))
    (hp : g (p c) = h (p c)) (hq : g (q c) = h (q c)) : g = h := by
  let _ := (g.comp (algebraMap R (Coordinate c))).toAlgebra
  let g' : Coordinate c →ₐ[R] T := ⟨g, fun _ ↦ rfl⟩
  let h' : Coordinate c →ₐ[R] T := ⟨h, fun a ↦ (hc a).symm⟩
  exact congrArg AlgHom.toRingHom (hom_ext c g' h' hp hq)

end FLT.Mazur.NodalFiber
