/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Linear and ring kernels under localization

The linear comparison identifies localization of the actual kernel with the
kernel of the localized map, with its localization-ring action. The ring
comparison identifies extended kernel ideals in commuting localization squares.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizedKernelComparison

section LinearKernels


variable {R M N P : Type*} [CommRing R] (S : Submonoid R)
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Localization respects composition with its localization-ring linear structures. -/
lemma map_comp (d : M →ₗ[R] N) (e : N →ₗ[R] P) :
    (LocalizedModule.map S e).comp (LocalizedModule.map S d) =
      LocalizedModule.map S (e.comp d) := by
  ext x
  induction x using LocalizedModule.induction_on with
  | h x s => simp only [LinearMap.comp_apply, LocalizedModule.map_mk]

/-- Exact localization, regarded as maps over the localization ring. -/
lemma map_exact (d : M →ₗ[R] N) (e : N →ₗ[R] P) (h : Function.Exact d e) :
    Function.Exact (LocalizedModule.map S d) (LocalizedModule.map S e) :=
  LocalizedModule.map_exact S d e h

/-- The localized inclusion, with codomain restricted to localized cycles. -/
def kernelMap (e : N →ₗ[R] P) :
    LocalizedModule S e.ker →ₗ[Localization S] (LocalizedModule.map S e).ker :=
  (LocalizedModule.map S e.ker.subtype).codRestrict _ (fun x ↦ by
    change ((LocalizedModule.map S e).comp (LocalizedModule.map S e.ker.subtype)) x = 0
    rw [map_comp, LinearMap.comp_ker_subtype, map_zero, LinearMap.zero_apply])

/-- The canonical cycle comparison is injective. -/
lemma kernelMap_injective (e : N →ₗ[R] P) : Function.Injective (kernelMap S e) := by
  intro x y h
  exact LocalizedModule.map_injective S e.ker.subtype e.ker.injective_subtype
    (congrArg Subtype.val h)

/-- Exactness supplies every localized cycle from a fraction of original cycles. -/
lemma kernelMap_surjective (e : N →ₗ[R] P) : Function.Surjective (kernelMap S e) := by
  intro x
  obtain ⟨y, hy⟩ := (map_exact S e.ker.subtype e (LinearMap.exact_subtype_ker_map e)
    x.val).mp x.property
  exact ⟨y, Subtype.ext hy⟩

/-- Localization of the actual kernel, with the correct localization-ring action. -/
def kernelEquiv (e : N →ₗ[R] P) :
    LocalizedModule S e.ker ≃ₗ[Localization S] (LocalizedModule.map S e).ker :=
  LinearEquiv.ofBijective (kernelMap S e)
    ⟨kernelMap_injective S e, kernelMap_surjective S e⟩

/-- The kernel comparison retains the ambient fraction. -/
lemma kernelEquiv_mk (e : N →ₗ[R] P) (x : e.ker) (s : S) :
    (kernelEquiv S e (LocalizedModule.mk x s)).val = LocalizedModule.mk x.val s :=
  LocalizedModule.map_mk S e.ker.subtype x s

end LinearKernels

section RingKernels


universe u v w z t

variable {S : Type u} {T : Type v} {U : Type w} {V : Type z}
  [CommRing S] [CommRing T] [CommRing U] [CommRing V]
  [Algebra S U] [Algebra T V]

/-- A commuting localization square computes the entire extended kernel. -/
theorem ker_eq_map_of_square (r : S) (f : S →+* T)
    [IsLocalization.Away r U] [IsLocalization.Away (f r) V]
    (g : U →+* V)
    (h : g.comp (algebraMap S U) = (algebraMap T V).comp f) :
    RingHom.ker g = (RingHom.ker f).map (algebraMap S U) := by
  have hg : g = IsLocalization.map V f
      ((Submonoid.map_powers f r).symm ▸ (Submonoid.powers r).le_comap_map) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    rw [IsLocalization.map_comp, h]
  rw [hg]
  exact IsLocalization.ker_map V f (Submonoid.map_powers f r)

variable {S' : Type t} [CommRing S']

/-- An equal two-edge path forces one kernel into the other localized kernel. -/
theorem map_ker_le_of_paths (r : S) (f : S →+* T)
    [IsLocalization.Away r U] [IsLocalization.Away (f r) V]
    (g : U →+* V)
    (h : g.comp (algebraMap S U) = (algebraMap T V).comp f)
    {T' : Type*} [CommRing T'] (f' : S' →+* T') (a : S' →+* U) (b : T' →+* V)
    (hp : g.comp a = b.comp f') :
    (RingHom.ker f').map a ≤ (RingHom.ker f).map (algebraMap S U) := by
  rw [← ker_eq_map_of_square r f g h, Ideal.map_le_iff_le_comap]
  intro x hx
  change g (a x) = 0
  rw [← RingHom.comp_apply, hp, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]

/-- If both comparison paths are localization squares, the extended kernels agree. -/
theorem map_ker_eq_of_squares [Algebra S' U]
    {T' : Type*} [CommRing T'] [Algebra T' V]
    (r : S) (r' : S') (f : S →+* T) (f' : S' →+* T')
    [IsLocalization.Away r U] [IsLocalization.Away (f r) V]
    [IsLocalization.Away r' U] [IsLocalization.Away (f' r') V]
    (g : U →+* V)
    (h : g.comp (algebraMap S U) = (algebraMap T V).comp f)
    (h' : g.comp (algebraMap S' U) = (algebraMap T' V).comp f') :
    (RingHom.ker f).map (algebraMap S U) =
      (RingHom.ker f').map (algebraMap S' U) := by
  rw [← ker_eq_map_of_square r f g h, ← ker_eq_map_of_square r' f' g h']

end RingKernels

end FLT.Mazur.LocalizedKernelComparison
