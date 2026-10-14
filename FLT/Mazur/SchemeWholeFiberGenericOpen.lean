/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstructibleGenericClosure
public import FLT.Mazur.SchemeWholeFiberOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Spreading whole generic fibers into actual target opens

Chevalley makes the image of the bad locus constructible. A whole good generic
fiber then lies over a nonempty open of the unchanged target. Irreducibility
is topological here: no reducedness or integrality assumption is imposed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace Topology Set
universe u
namespace FLT.Mazur.SchemeWholeFiberOpen
set_option backward.isDefEq.respectTransparency false
variable {K T : Scheme.{u}} (q : K ⟶ T) (L : K.Opens)
  [NoetherianSpace K] [LocallyOfFinitePresentation q] [QuasiCompact q]
  [CompactSpace T] [QuasiSeparatedSpace T]

/-- The image of the entire excluded locus is constructible, not merely its closed points. -/
theorem badImage_constructible : IsConstructible (q '' (L : Set K)ᶜ) :=
  q.isConstructible_image ((NoetherianSpace.isCompact (L : Set K)).isConstructible L.isOpen).compl

variable [IrreducibleSpace T]

/-- The canonical whole-fiber open contains the generic point iff its entire fiber is good. -/
theorem genericPoint_mem_iff : genericPoint T ∈ locus q L ↔
    ∀ x : K, q x = genericPoint T → x ∈ L := by
  change genericPoint T ∈ (closure (q '' (L : Set K)ᶜ))ᶜ ↔ _
  rw [ConstructibleGenericClosure.mem_compl_closure_iff
    (genericPoint_spec T) (badImage_constructible q L)]
  simp only [mem_image, mem_compl_iff, not_exists, not_and]
  constructor
  · intro h x hx
    by_contra hn
    exact h x hn hx
  · intro h x hn hx
    exact hn (h x hx)

/-- Nonemptiness requires only the original generic fiber, retaining every point above it. -/
theorem nonempty_iff_genericFiber : (locus q L : Set T).Nonempty ↔
    ∀ x : K, q x = genericPoint T → x ∈ L := by
  rw [← genericPoint_mem_iff q L]
  constructor
  · rintro ⟨y, hy⟩
    exact (genericPoint_specializes y).mem_open (locus q L).isOpen hy
  · intro h
    exact ⟨genericPoint T, h⟩

/-- A good complete generic fiber produces a dense open with unchanged scheme structure. -/
theorem dense_of_genericFiber (h : ∀ x : K, q x = genericPoint T → x ∈ L) :
    Dense (locus q L : Set T) :=
  (locus q L).isOpen.dense ((nonempty_iff_genericFiber q L).mpr h)

end FLT.Mazur.SchemeWholeFiberOpen
