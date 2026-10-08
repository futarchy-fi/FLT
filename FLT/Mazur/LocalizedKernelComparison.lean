/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Kernels in localized comparison squares

A commuting square between two genuine localizations identifies the kernel
of its upper map with the extended kernel of its lower map. A second path
through that square therefore gives compatibility of the two kernel ideals.
No compatibility of ideals is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizedKernelComparison

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

end FLT.Mazur.LocalizedKernelComparison
