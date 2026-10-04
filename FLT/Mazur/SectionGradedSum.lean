/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedMultiplication
public import Mathlib.Algebra.DirectSum.Module

/-!
# The full direct sum of tensor-power sections

All nonnegative degrees are present. Bilinear multiplication is extended
from the actual sheaf tensor by the direct-sum universal property. The ring
coherence laws, which are needed before applying Proj, remain separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum
universe u
namespace FLT.Mazur.SectionGradedSum
open SectionGradedMultiplication FCurve.ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)

/-- The full graded group of sections, with finite support in the degree. -/
abbrev Sections := ⨁ n : ℕ, Piece L U n

/-- Inclusion of all sections in a single degree. -/
abbrev of (n : ℕ) : Piece L U n →ₗ[Γ(X, U)] Sections L U :=
  DirectSum.lof Γ(X, U) ℕ (Piece L U) n

/-- Multiplication with a fixed left degree and arbitrary right support. -/
def row (m : ℕ) : Piece L U m →ₗ[Γ(X, U)] Sections L U →ₗ[Γ(X, U)] Sections L U where
  toFun s := DirectSum.toModule Γ(X, U) ℕ (Sections L U)
    (fun n ↦ (of L U (m + n)).comp (mul L U m n s))
  map_add' s t := by
    ext n a : 2
    simp
  map_smul' r s := by
    ext n a : 2
    simp

/-- Multiplication on arbitrary finite sums of sections in all degrees. -/
def product : Sections L U →ₗ[Γ(X, U)] Sections L U →ₗ[Γ(X, U)] Sections L U :=
  DirectSum.toModule Γ(X, U) ℕ (Sections L U →ₗ[Γ(X, U)] Sections L U) (row L U)

/-- Multiplication of homogeneous insertions is the actual section product. -/
lemma product_of (m n : ℕ) (s : Piece L U m) (t : Piece L U n) :
    product L U (of L U m s) (of L U n t) = of L U (m + n) (mul L U m n s t) := by
  simp [product, of, row]

/-- Left distributivity on the full graded group. -/
lemma product_add_left (a b c : Sections L U) :
    product L U (a + b) c = product L U a c + product L U b c :=
  LinearMap.congr_fun (map_add (product L U) a b) c

/-- Right distributivity on the full graded group. -/
lemma product_add_right (a b c : Sections L U) :
    product L U a (b + c) = product L U a b + product L U a c :=
  map_add (product L U a) b c

/-- The full multiplication is determined by its values on all homogeneous inputs. -/
lemma product_ext
    (b : Sections L U →ₗ[Γ(X, U)] Sections L U →ₗ[Γ(X, U)] Sections L U)
    (h : ∀ m n s t, b (of L U m s) (of L U n t) =
      of L U (m + n) (mul L U m n s t)) : b = product L U := by
  ext m s n t : 4
  exact (h m n s t).trans (product_of L U m n s t).symm

variable {U} {V : X.Opens}

/-- Restriction on the full direct sum, degree by degree. -/
def restrict (i : U ⟶ V) : Sections L V →+ Sections L U :=
  DirectSum.toAddMonoid (fun n ↦ (DirectSum.of (Piece L U) n).comp
    ((tensorPower L n).presheaf.map i.op).hom)

/-- Restriction preserves the homogeneous insertion. -/
lemma restrict_of (i : U ⟶ V) (n : ℕ) (s : Piece L V n) :
    restrict L i (of L V n s) = of L U n ((tensorPower L n).presheaf.map i.op s) :=
  DirectSum.toAddMonoid_of _ n s

/-- The full multiplication commutes with restriction, without support bounds. -/
lemma restrict_product (i : U ⟶ V) (a b : Sections L V) :
    restrict L i (product L V a b) =
      product L U (restrict L i a) (restrict L i b) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m s =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of n t =>
      change restrict L i (product L V (of L V m s) (of L V n t)) =
        product L U (restrict L i (of L V m s)) (restrict L i (of L V n t))
      rw [product_of, restrict_of, restrict_of, restrict_of, product_of, mul_restrict]
    | add b c hb hc =>
      simp only [map_add, hb, hc]
  | add a c ha hc =>
    simp only [map_add, LinearMap.add_apply, ha, hc]

end FLT.Mazur.SectionGradedSum
