/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedKernelComparison

/-!
# Localization of explicit linear homology

The canonical cycle comparison identifies the incoming images and thus induces
an isomorphism on cycles modulo boundaries, linear over the localization ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.LocalizedHomologyComparison
open LocalizedKernelComparison

variable {R M N P : Type*} [CommRing R] (S : Submonoid R)
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (d : M →ₗ[R] N) (e : N →ₗ[R] P) (h : e.comp d = 0)

/-- The incoming map with its target restricted to cycles. -/
def toCycles : M →ₗ[R] e.ker :=
  d.codRestrict _ (fun x ↦ LinearMap.congr_fun h x)

/-- The range in cycles is the incoming image pulled back along the inclusion. -/
lemma toCycles_range : (toCycles d e h).range = d.range.comap e.ker.subtype := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- The localized incoming map agrees with the cycle comparison in the ambient term. -/
lemma kernelEquiv_toCycles (x : LocalizedModule S M) :
    (kernelEquiv S e (LocalizedModule.map S (toCycles d e h) x)).val =
      LocalizedModule.map S d x := by
  induction x using LocalizedModule.induction_on with
  | h x s =>
    simp only [LocalizedModule.map_mk, kernelEquiv_mk]
    rfl

include h in
/-- The comparison carries localized boundaries onto the actual localized incoming image. -/
lemma boundaries_map :
    ((d.range.comap e.ker.subtype).localized S).map (kernelEquiv S e).toLinearMap =
      (LocalizedModule.map S d).range.comap (LocalizedModule.map S e).ker.subtype := by
  rw [← toCycles_range d e h]
  have hr : ((toCycles d e h).range).localized S =
      (LocalizedModule.map S (toCycles d e h)).range :=
    LinearMap.localized'_range_eq_range_localizedMap (Localization S) S
      (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S e.ker) _
  rw [hr]
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (kernelEquiv_toCycles S d e h z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨LocalizedModule.map S (toCycles d e h) z, ⟨z, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (kernelEquiv_toCycles S d e h z).trans hz

/-- Localization commutes with the explicit homology quotient, over the localized ring. -/
def homologyEquiv :
    LocalizedModule S (e.ker ⧸ d.range.comap e.ker.subtype) ≃ₗ[Localization S]
      ((LocalizedModule.map S e).ker ⧸
        (LocalizedModule.map S d).range.comap (LocalizedModule.map S e).ker.subtype) :=
  (localizedQuotientEquiv S (d.range.comap e.ker.subtype)).symm.trans
    (Submodule.Quotient.equiv _ _ (kernelEquiv S e) (boundaries_map S d e h))

end FLT.Mazur.LocalizedHomologyComparison
