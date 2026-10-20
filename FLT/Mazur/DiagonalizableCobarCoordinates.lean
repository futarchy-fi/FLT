/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!+# Integral coefficient maps for diagonalizable group obstructions

The character basis identifies functions on products of a diagonalizable group
with finitely supported coefficient arrays. Inserting zero gives pullback along
a projection; repeating a character gives pullback along multiplication. These
maps make sense with coefficients in any module, including a square-zero ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

variable (R M G : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Zero G]

/-- Pull a one-variable function back along the first projection. -/
def first : (G →₀ M) →ₗ[R] (G × G →₀ M) :=
  Finsupp.lmapDomain M R (fun a ↦ (a, 0))

/-- Pull a one-variable function back along the second projection. -/
def second : (G →₀ M) →ₗ[R] (G × G →₀ M) :=
  Finsupp.lmapDomain M R (fun a ↦ (0, a))

/-- Pull a character back along the diagonalizable group multiplication. -/
def diagonal : (G →₀ M) →ₗ[R] (G × G →₀ M) :=
  Finsupp.lmapDomain M R (fun a ↦ (a, a))

/-- The two-cochain associated with an additive coordinate correction. -/
def boundary : (G →₀ M) →ₗ[R] (G × G →₀ M) :=
  first R M G + second R M G - diagonal R M G

/-- Pull back along the projection onto the first two factors. -/
def front : (G × G →₀ M) →ₗ[R] ((G × G) × G →₀ M) :=
  Finsupp.lmapDomain M R (fun a ↦ (a, 0))

/-- Pull back along the projection onto the last two factors. -/
def back : (G × G →₀ M) →ₗ[R] ((G × G) × G →₀ M) :=
  Finsupp.lmapDomain M R (fun a ↦ ((0, a.1), a.2))

/-- Pull back a two-cochain by multiplication in the first two inputs. -/
def leftProduct : (G × G →₀ M) →ₗ[R] ((G × G) × G →₀ M) :=
  Finsupp.lmapDomain M R (fun a ↦ ((a.1, a.1), a.2))

/-- Pull back a two-cochain by multiplication in the last two inputs. -/
def rightProduct : (G × G →₀ M) →ₗ[R] ((G × G) × G →₀ M) :=
  Finsupp.lmapDomain M R (fun a ↦ ((a.1, a.2), a.2))

/-- Take the coefficient of the trivial character in the last input. -/
def contract : (G × G →₀ M) →ₗ[R] (G →₀ M) :=
  Finsupp.lcomapDomain (fun a ↦ (a, 0)) (fun _ _ h ↦ congrArg Prod.fst h)

/-- The same coefficient extraction on three inputs. -/
def contractThree : ((G × G) × G →₀ M) →ₗ[R] (G × G →₀ M) :=
  Finsupp.lcomapDomain (fun a ↦ (a, 0)) (fun _ _ h ↦ congrArg Prod.fst h)

/-- This is extraction of an actual coefficient, with no division by the group order. -/
theorem contract_apply (p : G × G →₀ M) (a : G) : contract R M G p a = p (a, 0) :=
  rfl

/-- Three-input contraction retains precisely the original coefficients at third index zero. -/
theorem contractThree_apply (p : (G × G) × G →₀ M) (a b : G) :
    contractThree R M G p (a, b) = p ((a, b), 0) := rfl

/-- A correction retains each of its three full character contributions. -/
theorem boundary_single (a : G) (m : M) :
    boundary R M G (Finsupp.single a m) =
      Finsupp.single (a, 0) m + Finsupp.single (0, a) m - Finsupp.single (a, a) m := by
  simp [boundary, first, second, diagonal, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

end FLT.Mazur.DiagonalizableCobar
