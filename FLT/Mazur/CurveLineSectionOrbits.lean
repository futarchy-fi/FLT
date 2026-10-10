/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveGenus
public import FLT.Mazur.LineSheafScalarAutomorphisms
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projective section classes and actual line automorphisms

When the global functions are the base field, two nonzero global sections
define the same projective point exactly when an actual line-sheaf
automorphism takes one to the other. This identifies the section orbits;
it does not yet construct their zero divisors or a representing scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafScalarEndomorphisms FLT.Mazur.IdealPowerScalarLift

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))

/-- Constant global functions identify base-field units with actual global units. -/
def constantGlobalUnitsEquiv (hc : HasConstantGlobalSections f) : kˣ ≃* Γ(X, ⊤)ˣ :=
  Units.mapEquiv (RingEquiv.ofBijective (structureScalarMap f) hc).toMulEquiv

/-- This comparison sends a field unit through the original structure map. -/
lemma constantGlobalUnitsEquiv_val (hc : HasConstantGlobalSections f) (a : kˣ) :
    (constantGlobalUnitsEquiv f hc a : Γ(X, ⊤)) = structureScalarMap f a := rfl

/-- Actual line automorphism orbits are exactly base-field scalar orbits on sections. -/
theorem line_section_iso_iff_scalar (hc : HasConstantGlobalSections f)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s t : Γ(L, ⊤)) :
    (∃ e : L ≅ L, e.hom.app ⊤ s = t) ↔
      ∃ a : kˣ, structureScalarMap f a • s = t := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨r, hr, _⟩ := existsUnique_scalarUnit hL e
    obtain ⟨a, rfl⟩ := (constantGlobalUnitsEquiv f hc).surjective r
    refine ⟨a, ?_⟩
    rw [← hr] at he
    change (scalarEnd L (structureScalarMap f a)).app ⊤ s = t at he
    simpa only [scalarEnd_app, show TopologicalSpace.Opens.leTop (⊤ : X.Opens) = 𝟙 ⊤ from rfl,
      op_id, X.presheaf.map_id, CommRingCat.id_apply] using he
  · rintro ⟨a, ha⟩
    refine ⟨scalarUnitIso L (constantGlobalUnitsEquiv f hc a), ?_⟩
    change (scalarEnd L (structureScalarMap f a)).app ⊤ s = t
    simpa only [scalarEnd_app, show TopologicalSpace.Opens.leTop (⊤ : X.Opens) = 𝟙 ⊤ from rfl,
      op_id, X.presheaf.map_id, CommRingCat.id_apply] using ha

/-- Projective equality of nonzero sections is exactly equivalence by an actual line isomorphism. -/
theorem projective_section_eq_iff_iso (hc : HasConstantGlobalSections f)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s t : Γ(L, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) :
    let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
    Projectivization.mk k s hs = Projectivization.mk k t ht ↔
      ∃ e : L ≅ L, e.hom.app ⊤ t = s := by
  let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
  change Projectivization.mk k s hs = Projectivization.mk k t ht ↔ _
  rw [Projectivization.mk_eq_mk_iff, line_section_iso_iff_scalar f hc hL]
  rfl

end FLT.Mazur.FCurve
