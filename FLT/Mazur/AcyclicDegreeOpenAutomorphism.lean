/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedAcyclicDegreeOpen

/-!
# Actual acyclic degree opens under original test automorphisms

The representing open transforms with the original Picard section. Thus
finite orbits of sections give finite orbits of the actual opens, without
postulating a second open or changing the coefficient base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {T U : Over (Spec (.of R))}

/-- Mapping the section maps every point of its actual acyclic degree open into the old open. -/
theorem acyclicDegreeOpen_map_le (b : U ⟶ T)
    (s : (relativeFppfSheaf f).obj.obj (op T)) (d : ℕ) :
    (unpointedAcyclicDegreeOpen f U ((relativeFppfSheaf f).obj.map b.op s) d : Set U.left) ⊆
      b.left ⁻¹' (unpointedAcyclicDegreeOpen f T s d : Set T.left) := by
  let j := unpointedAcyclicDegreeArrow f U ((relativeFppfSheaf f).obj.map b.op s) d
  have h := unpointedAcyclicDegreeArrow_mem f U ((relativeFppfSheaf f).obj.map b.op s) d
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at h
  obtain ⟨k, hk, _⟩ := (unpointedAcyclicDegreeOpen_represents f T s d (j ≫ b)).mp h
  rintro _ ⟨x, rfl⟩
  refine ⟨k.left x, ?_⟩
  exact congrArg (fun q ↦ q.left x) hk

/-- The actual acyclic degree open is equivariant for every original test isomorphism. -/
theorem acyclicDegreeOpen_iso (e : U ≅ T)
    (s : (relativeFppfSheaf f).obj.obj (op T)) (d : ℕ) :
    (unpointedAcyclicDegreeOpen f U ((relativeFppfSheaf f).obj.map e.hom.op s) d :
      Set U.left) = e.hom.left ⁻¹' (unpointedAcyclicDegreeOpen f T s d : Set T.left) := by
  apply Set.Subset.antisymm (acyclicDegreeOpen_map_le f e.hom s d)
  intro x hx
  have hs : (relativeFppfSheaf f).obj.map e.inv.op
      ((relativeFppfSheaf f).obj.map e.hom.op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      e.inv_hom_id, op_id, (relativeFppfSheaf f).obj.map_id]
    rfl
  have h := acyclicDegreeOpen_map_le f e.inv
    ((relativeFppfSheaf f).obj.map e.hom.op s) d
  rw [hs] at h
  have hh := h hx
  have he : e.inv.left (e.hom.left x) = x :=
    congrArg (fun q ↦ q.left x) e.hom_inv_id
  simpa only [Set.mem_preimage, he] using hh

/-- A finite orbit of original sections gives a finite orbit of their actual acyclic opens. -/
theorem acyclicDegreeOpen_finite_orbit {I : Type*} (e : I → (T ≅ T))
    (s : (relativeFppfSheaf f).obj.obj (op T)) (d : ℕ)
    (hs : (Set.range (fun i ↦ (relativeFppfSheaf f).obj.map (e i).hom.op s)).Finite) :
    (Set.range (fun i ↦ (e i).hom.left ⁻¹'
      (unpointedAcyclicDegreeOpen f T s d : Set T.left))).Finite := by
  have h := hs.image (fun c ↦ (unpointedAcyclicDegreeOpen f T c d : Set T.left))
  apply h.subset
  rintro _ ⟨i, rfl⟩
  exact ⟨_, ⟨i, rfl⟩, acyclicDegreeOpen_iso f (e i) s d⟩

end FLT.Mazur.CartierAbel
