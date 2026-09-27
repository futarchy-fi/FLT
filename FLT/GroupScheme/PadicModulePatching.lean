/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicLatticePatching
public import FLT.GroupScheme.PadicPatchingRings
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Finite projective module patching over localized integers

A finite projective module over `ℤ[1/(dp)]` and a full finite `ℤ_p`-lattice in its
local generic fibre patch to a finite projective module over `ℤ[1/d]`. Both base
changes are identified with the input modules, compatibly in the local field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.PadicPatching

universe u

variable (p : ℕ) [Fact p.Prime] (d : ℤ) [Fact (¬ (p : ℤ) ∣ d)]
    (M : Type u) [AddCommGroup M] [Module (Away d p) M]

/-- A finite projective global module with both prescribed base changes and the
compatibility on their common local generic fibre. -/
structure ModulePatch (L : Submodule ℤ_[p] (ℚ_[p] ⊗[Away d p] M)) where
  /-- The patched module over `ℤ[1/d]`. -/
  Carrier : Type u
  /-- The additive group of the patched module. -/
  [addCommGroup : AddCommGroup Carrier]
  /-- The scalar action of the global base ring. -/
  [module : Module (Base d) Carrier]
  /-- The patched module is finitely generated. -/
  [finite : Module.Finite (Base d) Carrier]
  /-- The patched module is projective. -/
  [projective : Module.Projective (Base d) Carrier]
  /-- Inverting `p` recovers the original module. -/
  awayEquiv : Away d p ⊗[Base d] Carrier ≃ₗ[Away d p] M
  /-- Completing at `p` recovers the prescribed lattice. -/
  localEquiv : ℤ_[p] ⊗[Base d] Carrier ≃ₗ[ℤ_[p]] L
  /-- The two comparisons agree in the common generic fibre. -/
  compatible : ∀ x : Carrier,
    (1 : ℚ_[p]) ⊗ₜ[Away d p] awayEquiv (1 ⊗ₜ[Base d] x) =
      (localEquiv (1 ⊗ₜ[Base d] x)).val

attribute [instance] ModulePatch.addCommGroup ModulePatch.module
  ModulePatch.finite ModulePatch.projective

/-- Patch a finite projective module and an arbitrary full local lattice.
No rationality assumption on a basis of the local lattice is needed. -/
def patchModule [Module.Finite (Away d p) M] [Module.Projective (Away d p) M]
    (L : Submodule ℤ_[p] (ℚ_[p] ⊗[Away d p] M)) (hL : L.FG)
    (hspan : Submodule.span ℚ_[p] (L : Set (ℚ_[p] ⊗[Away d p] M)) = ⊤) :
    ModulePatch p d M L := by
  classical
  let : NeZero d := ⟨denominator_ne_zero p d⟩
  let R := Base d
  let S := Away d p
  let ι := Module.Free.ChooseBasisIndex S M
  let b := Module.Free.chooseBasis S M
  let := Fintype.ofFinite ι
  let e : M ≃ₗ[S] (ι → S) := b.equivFun
  let f : ℚ_[p] ⊗[S] M ≃ₗ[ℚ_[p]] (ι → ℚ_[p]) :=
    (e.baseChange S ℚ_[p] M (ι → S)).trans (TensorProduct.piScalarRight S ℚ_[p] ℚ_[p] ι)
  have hf (x : M) (i : ι) : f (1 ⊗ₜ[S] x) i = algebraMap S ℚ_[p] (e x i) := by
    simp [f, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def]
  let L' : Submodule ℤ_[p] (ι → ℚ_[p]) := L.map (f.restrictScalars ℤ_[p]).toLinearMap
  have hL' : L'.FG := hL.map _
  have hspan' : Submodule.span ℚ_[p] (L' : Set (ι → ℚ_[p])) = ⊤ := by
    change Submodule.span ℚ_[p] (f.toLinearMap '' (L : Set _)) = ⊤
    rw [← Submodule.map_span f.toLinearMap, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr f.surjective
  let N := padicIntersection p R S L'
  let : Module.Finite R N := padicIntersection_finite p R S d L' hL'
  let : Module.Projective R N := padicIntersection_projective p R S d L' hL'
  let a := padicIntersectionAwayEquiv p R S L' hspan'
  let l := padicIntersectionLocalEquiv p R S d L' hspan'
  let t : L ≃ₗ[ℤ_[p]] L' :=
    Submodule.equivMapOfInjective (f.restrictScalars ℤ_[p]).toLinearMap f.injective L
  refine { Carrier := N
           awayEquiv := a.trans e.symm
           localEquiv := l.trans t.symm
           compatible := ?_ }
  intro x
  apply f.injective
  have ht (z : L') : f (t.symm z).val = z.val := by
    exact congrArg Subtype.val (t.apply_symm_apply z)
  change f (1 ⊗ₜ[S] e.symm (a (1 ⊗ₜ[R] x))) = f (t.symm (l (1 ⊗ₜ[R] x))).val
  rw [ht]
  ext i
  rw [hf]
  simp [a, l, padicIntersectionAwayEquiv_tmul, padicIntersectionLocalEquiv_tmul]

/-- Existence form of finite projective patching. -/
theorem nonempty_modulePatch [Module.Finite (Away d p) M]
    [Module.Projective (Away d p) M]
    (L : Submodule ℤ_[p] (ℚ_[p] ⊗[Away d p] M)) (hL : L.FG)
    (hspan : Submodule.span ℚ_[p] (L : Set (ℚ_[p] ⊗[Away d p] M)) = ⊤) :
    Nonempty (ModulePatch p d M L) := ⟨patchModule p d M L hL hspan⟩

/-- Three does not divide the denominator inverted away from two. -/
instance threeNotDvdTwo : Fact (¬ ((3 : ℕ) : ℤ) ∣ (2 : ℤ)) := ⟨by norm_num⟩

/-- The module-level arithmetic patching theorem over `ℤ[1/2]`.
`Away 2 3` is the localization `ℤ[1/6]`, realized in two steps. -/
theorem module_patch_away_two (M : Type u) [AddCommGroup M] [Module (Away 2 3) M]
    [Module.Finite (Away 2 3) M] [Module.Projective (Away 2 3) M]
    (L : Submodule ℤ_[3] (ℚ_[3] ⊗[Away 2 3] M)) (hL : L.FG)
    (hspan : Submodule.span ℚ_[3] (L : Set (ℚ_[3] ⊗[Away 2 3] M)) = ⊤) :
    Nonempty (ModulePatch 3 2 M L) := nonempty_modulePatch 3 2 M L hL hspan

end ThreeAdicPlan.PadicPatching
