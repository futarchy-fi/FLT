/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatAlgebraEqualizer

/-!
# Naturality of the full flat equalizer comparison

A map of full two-endpoint diagrams induces a map of invariant algebras.
Flat extension commutes with this map, retaining both independent endpoint
equations. In particular this applies to restriction to an invariant boundary.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatAlgebraEqualizer
variable {R A C A' C' : Type*}
  [CommRing R] [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
  [Algebra R A] [Algebra R C] [Algebra R A'] [Algebra R C']
  (p q : A →ₐ[R] C) (p' q' : A' →ₐ[R] C')
  (u : A →ₐ[R] A') (v : C →ₐ[R] C')
  (hp : p'.comp u = v.comp p) (hq : q'.comp u = v.comp q)

/-- The original map of full invariant algebras uses the unchanged source restriction. -/
def equalizerMap : AlgHom.equalizer p q →ₐ[R] AlgHom.equalizer p' q' :=
  (u.comp (AlgHom.equalizer p q).val).codRestrict _ fun a ↦ by
    change p' (u a.val) = q' (u a.val)
    calc
      p' (u a.val) = v (p a.val) := DFunLike.congr_fun hp a.val
      _ = v (q a.val) := congrArg v a.property
      _ = q' (u a.val) := (DFunLike.congr_fun hq a.val).symm

/-- The induced invariant map retains exactly the original source coefficient map. -/
theorem equalizerMap_val (a : AlgHom.equalizer p q) :
    (equalizerMap p q p' q' u v hp hq a).val = u a.val := rfl

variable (S : Type*) [CommRing S] [Algebra R S]

/-- A full endpoint square remains commutative after any ground extension. -/
theorem tensorMap_square (h : p'.comp u = v.comp p) :
    (tensorMap S p').comp (tensorMap S u) =
      (tensorMap S v).comp (tensorMap S p) := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s a => exact congrArg (fun c ↦ s ⊗ₜ[R] c) (DFunLike.congr_fun h a)
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Restriction on the full tensor equalizers, retaining both endpoint squares. -/
def tensorEqualizerMap :
    AlgHom.equalizer (tensorMap S p) (tensorMap S q) →ₐ[S]
      AlgHom.equalizer (tensorMap S p') (tensorMap S q') :=
  equalizerMap _ _ _ _ (tensorMap S u) (tensorMap S v)
    (tensorMap_square p p' u v S hp) (tensorMap_square q q' u v S hq)

/-- Naturality holds already for the canonical comparison maps, before flatness is used. -/
theorem comparisonMap_natural (x : S ⊗[R] AlgHom.equalizer p q) :
    tensorEqualizerMap p q p' q' u v hp hq S (comparisonMap p q S x) =
      comparisonMap p' q' S (tensorMap S (equalizerMap p q p' q' u v hp hq) x) := by
  apply Subtype.ext
  induction x using TensorProduct.inductionOn with
  | tmul s a => rfl
  | add x y hx hy =>
      simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (· + ·) hx hy

variable [Module.Flat R S]

/-- The flat algebra equivalences commute with actual restriction to the boundary. -/
theorem comparison_natural (x : S ⊗[R] AlgHom.equalizer p q) :
    tensorEqualizerMap p q p' q' u v hp hq S (comparison p q S x) =
      comparison p' q' S (tensorMap S (equalizerMap p q p' q' u v hp hq) x) :=
  comparisonMap_natural p q p' q' u v hp hq S x

end FLT.Mazur.FlatAlgebraEqualizer
