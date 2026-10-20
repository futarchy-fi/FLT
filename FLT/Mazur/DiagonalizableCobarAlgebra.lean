/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableCobarContraction
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!+# Cobar contraction on the actual diagonalizable coordinate algebra

The character-array maps are the algebra maps for projections and group
multiplication. The latter agrees with the original Hopf comultiplication
under the tensor-product coordinate equivalence.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

open scoped TensorProduct

variable (R G : Type*) [CommRing R] [AddCommMonoid G]

/-- The actual coordinate map of the first projection. -/
def firstMap : AddMonoidAlgebra R G →ₐ[R] AddMonoidAlgebra R (G × G) :=
  AddMonoidAlgebra.mapDomainAlgHom R R
    ⟨⟨fun a ↦ (a, 0), rfl⟩, fun _ _ ↦ by simp⟩

/-- The actual coordinate map of the second projection. -/
def secondMap : AddMonoidAlgebra R G →ₐ[R] AddMonoidAlgebra R (G × G) :=
  AddMonoidAlgebra.mapDomainAlgHom R R
    ⟨⟨fun a ↦ (0, a), rfl⟩, fun _ _ ↦ by simp⟩

/-- The actual coordinate map of group multiplication. -/
def diagonalMap : AddMonoidAlgebra R G →ₐ[R] AddMonoidAlgebra R (G × G) :=
  AddMonoidAlgebra.mapDomainAlgHom R R
    ⟨⟨fun a ↦ (a, a), rfl⟩, fun _ _ ↦ rfl⟩

/-- The actual first-pair projection on coordinate rings. -/
def frontMap : AddMonoidAlgebra R (G × G) →ₐ[R]
    AddMonoidAlgebra R ((G × G) × G) :=
  AddMonoidAlgebra.mapDomainAlgHom R R
    ⟨⟨fun a ↦ (a, 0), rfl⟩, fun _ _ ↦ by simp⟩

/-- The actual last-pair projection on coordinate rings. -/
def backMap : AddMonoidAlgebra R (G × G) →ₐ[R]
    AddMonoidAlgebra R ((G × G) × G) :=
  AddMonoidAlgebra.mapDomainAlgHom R R
    ⟨⟨fun a ↦ ((0, a.1), a.2), rfl⟩, fun _ _ ↦ by simp⟩

/-- The actual coordinate map multiplying the first two inputs. -/
def leftProductMap : AddMonoidAlgebra R (G × G) →ₐ[R]
    AddMonoidAlgebra R ((G × G) × G) :=
  AddMonoidAlgebra.mapDomainAlgHom R R
    ⟨⟨fun a ↦ ((a.1, a.1), a.2), rfl⟩, fun _ _ ↦ rfl⟩

/-- The actual coordinate map multiplying the last two inputs. -/
def rightProductMap : AddMonoidAlgebra R (G × G) →ₐ[R]
    AddMonoidAlgebra R ((G × G) × G) :=
  AddMonoidAlgebra.mapDomainAlgHom R R
    ⟨⟨fun a ↦ ((a.1, a.2), a.2), rfl⟩, fun _ _ ↦ rfl⟩

/-- Extract the full correction as an element of the original coordinate algebra. -/
def correction (p : AddMonoidAlgebra R (G × G)) : AddMonoidAlgebra R G :=
  .ofCoeff (contract R R G p.coeff)

/-- Each correction coefficient is the original coefficient at trivial second character. -/
theorem correction_coeff (p : AddMonoidAlgebra R (G × G)) (a : G) :
    (correction R G p).coeff a = p.coeff (a, 0) := rfl

/-- The coordinate formula uses the genuine Hopf multiplication map. -/
theorem diagonalMap_comul (q : AddMonoidAlgebra R G) :
    diagonalMap R G q = AddMonoidAlgebra.tensorEquiv R (Coalgebra.comul q) := by
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single a r =>
    simp [diagonalMap, AddMonoidAlgebra.comul_single]

/-- The full algebra-valued associativity defect has the explicit integral correction. -/
theorem algebra_cocycle_eq (p : AddMonoidAlgebra R (G × G))
    (hp : frontMap R G p + leftProductMap R G p =
      backMap R G p + rightProductMap R G p) :
    p = firstMap R G (correction R G p) + secondMap R G (correction R G p) -
      diagonalMap R G (correction R G p) := by
  apply AddMonoidAlgebra.coeff_injective
  exact cocycle_eq_boundary R R G p.coeff (congrArg AddMonoidAlgebra.coeff hp)

end FLT.Mazur.DiagonalizableCobar
