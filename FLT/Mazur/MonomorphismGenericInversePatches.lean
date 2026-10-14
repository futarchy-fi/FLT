/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismRelativeOpen
public import FLT.Mazur.SchemeWholeFiberGenericOpen

/-!
# Finite original inverse patches over a whole generic fiber

For a finitely presented Noetherian kernel, its effective target open is
nonempty exactly when finitely many actual inverse patches cover the complete
generic fiber. These patches carry inverses of scheme morphisms; equality on
residue fields or on a reduced fiber is not used as a substitute.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Set
universe u
namespace FLT.Mazur.MonomorphismRelativeOpen
variable {D K T : Scheme.{u}} (m : D ⟶ K) (q : K ⟶ T)
  [NoetherianSpace K] [LocallyOfFinitePresentation q] [QuasiCompact q]
  [CompactSpace T] [QuasiSeparatedSpace T] [IrreducibleSpace T]

/-- The effective target is nonempty iff every generic kernel point has an inverse.
The inverse is defined on an original scheme open, with its full structure sheaf. -/
theorem targetOpen_nonempty_iff_genericFiber : (targetOpen m q : Set T).Nonempty ↔
    ∀ x : K, q x = genericPoint T → x ∈ MonomorphismOpenImage.locus m :=
  SchemeWholeFiberOpen.nonempty_iff_genericFiber q (MonomorphismOpenImage.locus m)

/-- Finitely many original inverse patches are necessary and sufficient over the generic fiber.
No inverse or effectivity field is added to the model data. -/
theorem targetOpen_nonempty_iff_finite_patches : (targetOpen m q : Set T).Nonempty ↔
    ∃ s : Finset (MonomorphismOpenImage.Patches m),
      ∀ x : K, q x = genericPoint T → ∃ U ∈ s, x ∈ U.val := by
  rw [targetOpen_nonempty_iff_genericFiber m q]
  constructor
  · intro h
    have hc : {x : K | q x = genericPoint T} ⊆
        ⋃ U : MonomorphismOpenImage.Patches m, (U.val : Set K) := by
      intro x hx
      obtain ⟨U, hU⟩ := Opens.mem_iSup.mp (h x hx)
      exact mem_iUnion.mpr ⟨U, hU⟩
    obtain ⟨s, hs⟩ :=
      (NoetherianSpace.isCompact {x : K | q x = genericPoint T}).elim_finite_subcover
        (fun U : MonomorphismOpenImage.Patches m ↦ (U.val : Set K))
        (fun U ↦ U.val.isOpen) hc
    refine ⟨s, fun x hx ↦ ?_⟩
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact ⟨U, hU, hxU⟩
  · rintro ⟨s, hs⟩ x hx
    obtain ⟨U, _, hU⟩ := hs x hx
    exact MonomorphismOpenImage.patch_le m U hU

/-- A finite cover of the generic kernel constructs a dense effective target open. -/
theorem targetOpen_dense_of_finite_patches
    (s : Finset (MonomorphismOpenImage.Patches m))
    (hs : ∀ x : K, q x = genericPoint T → ∃ U ∈ s, x ∈ U.val) :
    Dense (targetOpen m q : Set T) :=
  (targetOpen m q).isOpen.dense
    ((targetOpen_nonempty_iff_finite_patches m q).mpr ⟨s, hs⟩)

end FLT.Mazur.MonomorphismRelativeOpen
