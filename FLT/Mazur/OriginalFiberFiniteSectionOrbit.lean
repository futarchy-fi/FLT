/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalFiniteCoefficientOrbit
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Finite orbits of translated sections on the original geometric fiber

The complete semilinear action fixes the original translation section.
A geometric input pulled back from finite coefficients therefore gives a
finite orbit of its product with that translation in the original presheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OriginalFiberFiniteSectionOrbit
open OriginalFiniteCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] {S : Scheme} (t : Spec (.of k) ⟶ S)
  {V Y : Over S} (a : Y ⟶ V) (b : Y ⟶ coefficientTest (K := K) t)
  (H : IsPullback a.left b.left V.hom (coefficientTest (K := K) t).hom)

/-- The actual fiber automorphism is an isomorphism over the original base. -/
def fiberIso (σ : K ≃ₐ[k] K) : Y ≅ Y :=
  Over.isoMk (ResidueGeometricConjugacy.fiberAction t H σ) (by
    rw [← a.w, ← Category.assoc, ResidueGeometricConjugacy.fiberAction_fst])

@[reassoc]
theorem fiberIso_fst (σ : K ≃ₐ[k] K) : (fiberIso t a b H σ).hom ≫ a = a :=
  Over.OverMorphism.ext (ResidueGeometricConjugacy.fiberAction_fst t H σ)

@[reassoc]
theorem fiberIso_snd (σ : K ≃ₐ[k] K) :
    (fiberIso t a b H σ).hom ≫ b = b ≫ (coefficientIso t σ).hom :=
  Over.OverMorphism.ext (ResidueGeometricConjugacy.fiberAction_snd t H σ)

variable (F : (Over S)ᵒᵖ ⥤ CommGrpCat)

/-- The semilinear action changes only the geometric input, fixing the original translation. -/
theorem translated_section_conjugate
    (s : F.obj (op (coefficientTest (K := K) t))) (c : F.obj (op V)) (σ : K ≃ₐ[k] K) :
    F.map (fiberIso t a b H σ).hom.op (F.map b.op s * F.map a.op c) =
      F.map b.op (F.map (coefficientIso t σ).hom.op s) * F.map a.op c := by
  have hcomp {A B C : Over S} (p : A ⟶ B) (q : B ⟶ C) (x : F.obj (op C)) :
      F.map p.op (F.map q.op x) = F.map (p ≫ q).op x := by
    rw [op_comp, F.map_comp]
    rfl
  rw [map_mul, hcomp, hcomp, fiberIso_fst, fiberIso_snd, ← hcomp]

/-- Finite coefficient descent proves finite orbit of the entire translated section. -/
theorem finite_translated_section_orbit [Module.Finite k L] (i : L →ₐ[k] K)
    (s : F.obj (op (coefficientTest (K := L) t))) (c : F.obj (op V)) :
    (Set.range (fun σ : K ≃ₐ[k] K ↦ F.map (fiberIso t a b H σ).hom.op
      (F.map b.op (F.map (restriction t i).op s) * F.map a.op c))).Finite := by
  have h := finite_original_section_orbit t i (F ⋙ forget CommGrpCat) s
  have hh := h.image (fun v ↦ F.map b.op v * F.map a.op c)
  apply hh.subset
  rintro _ ⟨σ, rfl⟩
  exact ⟨_, ⟨σ, rfl⟩, (translated_section_conjugate t a b H F _ c σ).symm⟩

end FLT.Mazur.OriginalFiberFiniteSectionOrbit
