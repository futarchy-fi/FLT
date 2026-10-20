/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassDiagonalizableDefect

/-!
# Character defects under arbitrary coefficient maps

Changing coefficients commutes with every character coface and hence with the
full multiplication defect. Invertible coefficient changes detect equality of
the original smooth-group points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open WeierstrassIntegralChart DiagonalizableCobar

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S T G H : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [AddCommMonoid G] [AddCommMonoid H]
  (W : WeierstrassCurve R)

/-- Coefficient change commutes with every character substitution. -/
theorem coefficientMap_mapDomain (f : S →ₐ[R] T) (g : G →+ H) :
    (AddMonoidAlgebra.mapAlgHom H f).comp
        ((AddMonoidAlgebra.mapDomainAlgHom S S g).restrictScalars R) =
      ((AddMonoidAlgebra.mapDomainAlgHom T T g).restrictScalars R).comp
        (AddMonoidAlgebra.mapAlgHom G f) := by
  apply AlgHom.coe_ringHom_injective
  exact AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom f.toRingHom g

/-- The actual multiplication error commutes with arbitrary coefficient change. -/
theorem defect_coefficientMap (f : S →ₐ[R] T) (p : Points W (AddMonoidAlgebra S G)) :
    defect W (smoothAlgebraReduction W (AddMonoidAlgebra.mapAlgHom G f) p) =
      smoothAlgebraReduction W (AddMonoidAlgebra.mapAlgHom (G × G) f) (defect W p) := by
  rw [defect, defect, map_div, map_mul]
  simp only [firstMap, secondMap, diagonalMap, ← smoothAlgebraReduction_comp,
    coefficientMap_mapDomain]

/-- An identity test-algebra map acts as the identity on original points. -/
theorem smoothAlgebraReduction_id (A : Type u) [CommRing A] [Algebra R A]
    (p : Points W A) : smoothAlgebraReduction W (AlgHom.id R A) p = p := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ p.left = p.left
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- Inverse coefficient changes recover the entire original point. -/
theorem coefficientEquiv_roundtrip (e : S ≃ₐ[R] T) (p : Points W (AddMonoidAlgebra S G)) :
    smoothAlgebraReduction W (AddMonoidAlgebra.mapAlgHom G e.symm.toAlgHom)
      (smoothAlgebraReduction W (AddMonoidAlgebra.mapAlgHom G e.toAlgHom) p) = p := by
  rw [← smoothAlgebraReduction_comp, ← AddMonoidAlgebra.mapRangeAlgHom_comp]
  simp only [AlgEquiv.symm_comp, AddMonoidAlgebra.mapAlgHom_id]
  exact smoothAlgebraReduction_id W _ p

/-- Coefficient equivalences lose no equality of actual smooth-group points. -/
theorem coefficientEquiv_injective (e : S ≃ₐ[R] T) :
    Function.Injective (smoothAlgebraReduction W (AddMonoidAlgebra.mapAlgHom G e.toAlgHom)) := by
  intro p q h
  have := congrArg
    (smoothAlgebraReduction W (AddMonoidAlgebra.mapAlgHom G e.symm.toAlgHom)) h
  simpa only [coefficientEquiv_roundtrip] using this

end FLT.Mazur.WeierstrassDiagonalizableDefect
