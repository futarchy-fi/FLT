/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPairEffectiveOpen
public import FLT.Mazur.MonomorphismGenericInversePatches

/-!
# Generic full-kernel criteria for effective target neighborhoods

The candidate kernel inherits finite presentation and Noetherianity from the
actual coefficient projection. Its full relation becomes effective on a
nonempty original target open precisely when finitely many genuine inverse
patches cover the whole generic kernel fiber. The target may be nonreduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme} (p q : D ⟶ A) (w : A ⟶ T) (h : p ≫ w = q ≫ w)
  [IsNoetherian A] [IsNoetherian T] [LocallyOfFinitePresentation w] [QuasiCompact w]
  [IrreducibleSpace T]
local notation "m" => pullback.lift p q h
local notation "v" => pullback.fst w w ≫ w
local instance genericEffectiveKernelNoetherian : IsNoetherian (pullback w w) := ⟨⟩

/-- Nonemptiness is equivalent to local inverses at every generic kernel point. -/
theorem targetOpen_nonempty_iff_genericFiber : (targetOpen p q w h : Set T).Nonempty ↔
    ∀ x : (pullback w w : Scheme), v x = genericPoint T → x ∈ MonomorphismOpenImage.locus m :=
  SchemeWholeFiberOpen.nonempty_iff_genericFiber v (MonomorphismOpenImage.locus m)

/-- The generic obstruction can be checked on finitely many original inverse patches. -/
theorem targetOpen_nonempty_iff_finite_patches : (targetOpen p q w h : Set T).Nonempty ↔
    ∃ s : Finset (MonomorphismOpenImage.Patches m),
      ∀ x : (pullback w w : Scheme), v x = genericPoint T → ∃ U ∈ s, x ∈ U.val :=
  MonomorphismRelativeOpen.targetOpen_nonempty_iff_finite_patches m v

/-- Finite generic inverse data gives a dense target with an effective full relation. -/
theorem targetOpen_dense_of_finite_patches
    (s : Finset (MonomorphismOpenImage.Patches m))
    (hs : ∀ x : (pullback w w : Scheme), v x = genericPoint T → ∃ U ∈ s, x ∈ U.val) :
    Dense (targetOpen p q w h : Set T) :=
  MonomorphismRelativeOpen.targetOpen_dense_of_finite_patches m v s hs

end FLT.Mazur.KernelPairEffectiveOpen
