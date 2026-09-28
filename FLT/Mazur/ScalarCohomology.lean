/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Scalar cohomology of the structure sheaf

The coefficients are the underlying abelian sheaf of `SheafOfModules.unit X.ringCatSheaf`.
Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, with scalars acting through multiplication
endomorphisms of this sheaf. Its degree-zero comparison is `Sheaf.H.equiv₀`, and linearity
follows from `Sheaf.H.equiv₀_naturality`.

This supplies the scalar interface in FC07 of `docs/FCURVE_CONTRACTS.md`. The genus and
finite-dimensionality results in Stacks 0BY7 and 02O6 require additional geometric arguments.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.FCurve

local instance structureHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- The structure sheaf regarded as a sheaf of modules over itself. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The actual structure sheaf with only its additive structure retained. -/
abbrev structureAbelianSheaf (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (structureModule X)

/-- Structure-sheaf cohomology in any nonnegative degree. -/
abbrev StructureH (X : Scheme.{u}) (n : ℕ) : Type (u + 1) :=
  Sheaf.H (structureAbelianSheaf X) n

/-- Multiplication by the restrictions of a global section. -/
def structureMultiply (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    structureAbelianSheaf X ⟶ structureAbelianSheaf X where
  hom :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun (x : Γ(X, U.unop)) ↦
            X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r * x
          map_zero' := mul_zero (M₀ := Γ(X, U.unop)) _
          map_add' := mul_add (R := Γ(X, U.unop)) _ }
      naturality := by
        intro U V i
        ext x
        change Γ(X, U.unop) at x
        symm
        change X.presheaf.map i
            (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r * x) =
          X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op r * X.presheaf.map i x
        rw [map_mul]
        congr 1
        exact congr($((X.presheaf.map_comp (homOfLE le_top).op i).symm) r) }

@[simp]
lemma structureMultiply_one (X : Scheme.{u}) : structureMultiply X 1 = 𝟙 _ := by
  ext U x
  change Γ(X, U.unop) at x
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op 1 * x = x
  simp

@[simp]
lemma structureMultiply_add (X : Scheme.{u}) (r s : Γ(X, ⊤)) :
    structureMultiply X (r + s) = structureMultiply X r + structureMultiply X s := by
  ext U x
  change Γ(X, U.unop) at x
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (r + s) * x =
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r * x +
      X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s * x
  simp [add_mul]

lemma structureMultiply_mul (X : Scheme.{u}) (r s : Γ(X, ⊤)) :
    structureMultiply X (r * s) = structureMultiply X s ≫ structureMultiply X r := by
  ext U x
  change Γ(X, U.unop) at x
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (r * s) * x =
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r *
      (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s * x)
  simp [mul_assoc]

/-- Multiplication induces a ring action on cohomology. -/
def structureHAction (X : Scheme.{u}) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (StructureH X n) where
  toFun r := Sheaf.H.map (structureMultiply X r) n
  map_one' := by
    ext x
    change Sheaf.H.map (structureMultiply X 1) n x = x
    rw [structureMultiply_one, Sheaf.H.map_id_apply]
  map_mul' r s := by
    ext x
    change Sheaf.H.map (structureMultiply X (r * s)) n x =
      Sheaf.H.map (structureMultiply X r) n (Sheaf.H.map (structureMultiply X s) n x)
    rw [structureMultiply_mul, Sheaf.H.map_comp_apply]
  map_add' r s := by
    ext x
    exact congrArg (fun f ↦ Sheaf.H.map f n x) (structureMultiply_add X r s) |>.trans
      (Sheaf.H.map_add_apply _ _ x)
  map_zero' := by
    ext x
    have h : structureMultiply X 0 = 0 := by
      ext U y
      change Γ(X, U.unop) at y
      change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op 0 * y = 0
      simp
    change Sheaf.H.map (structureMultiply X 0) n x = 0
    simp [h, Sheaf.H.map]

/-- The global-section action on cohomology is induced on the coefficient sheaf. -/
instance structureHModule (X : Scheme.{u}) (n : ℕ) : Module Γ(X, ⊤) (StructureH X n) :=
  Module.compHom (StructureH X n) (structureHAction X n)

/-- Degree-zero cohomology agrees with the genuine global sections, linearly. -/
def structureH0Equiv (X : Scheme.{u}) : StructureH X 0 ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) where
  toAddEquiv := Sheaf.H.equiv₀ (structureAbelianSheaf X) isTerminalTop
  map_smul' r x := by
    change Sheaf.H.equiv₀ (structureAbelianSheaf X) isTerminalTop
        (Sheaf.H.map (structureMultiply X r) 0 x) = _
    rw [← Sheaf.H.equiv₀_naturality isTerminalTop (structureMultiply X r)]
    change X.presheaf.map (𝟙 (op ⊤)) r * _ = r * _
    simp

section Scalars

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The scalar map on global sections, determined by the specified structure morphism. -/
def structureScalarMap (f : X ⟶ Spec (CommRingCat.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom

/-- Cohomology with its specified base morphism retained in the type. -/
def ScalarH (_f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) : Type (u + 1) :=
  StructureH X n

instance scalarHAddCommGroup (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    AddCommGroup (ScalarH f n) :=
  inferInstanceAs (AddCommGroup (StructureH X n))

/-- The field action is restriction of the canonical global-section action. -/
instance scalarHModule (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    Module k (ScalarH f n) :=
  Module.compHom (StructureH X n) (structureScalarMap f)

/-- Zeroth cohomology of the structure sheaf of a scheme over a field. -/
abbrev H0 (f : X ⟶ Spec (CommRingCat.of k)) := ScalarH f 0

/-- First cohomology of the structure sheaf of a scheme over a field. -/
abbrev H1 (f : X ⟶ Spec (CommRingCat.of k)) := ScalarH f 1

/-- Forgetting the named base morphism recovers Mathlib's cohomology, additively. -/
def scalarHAddEquiv (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    ScalarH f n ≃+ Sheaf.H (structureAbelianSheaf X) n :=
  AddEquiv.refl _

/-- Scalar multiplication is induced by multiplication on the actual coefficient sheaf. -/
lemma scalarH_smul (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    (a : k) (x : ScalarH f n) :
    scalarHAddEquiv f n (a • x) =
      Sheaf.H.map (structureMultiply X (structureScalarMap f a)) n
        (scalarHAddEquiv f n x) := rfl

/-- The canonical comparison with global sections, with their action through the base map. -/
def scalarH0Equiv (f : X ⟶ Spec (CommRingCat.of k)) :
    letI := Module.compHom Γ(X, ⊤) (structureScalarMap f)
    H0 f ≃ₗ[k] Γ(X, ⊤) := by
  letI := Module.compHom Γ(X, ⊤) (structureScalarMap f)
  exact
    { toAddEquiv := scalarHAddEquiv f 0 |>.trans (structureH0Equiv X).toAddEquiv
      map_smul' := fun a x ↦ (structureH0Equiv X).map_smul (structureScalarMap f a) x }

end Scalars

end FLT.Mazur.FCurve
