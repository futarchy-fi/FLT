/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedLineIsomorphisms
public import FLT.Mazur.LineSheafScalarAutomorphisms

/-!
# Correcting a line isomorphism to preserve rigidifications

A section lifts every scalar automorphism from the base. Correcting an
arbitrary line isomorphism by such a lift makes it preserve the two specified
trivializations. No descent or uniqueness hypothesis is needed for existence.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve.LineSheafSectionRigidity
open ModuleSheafScalarEndomorphisms IdealPowerScalarLift
variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include hs in
/-- Every automorphism of a restricted line sheaf lifts along the chosen section. -/
theorem exists_iso_pullback_eq {M : X.Modules} (hM : LocallyFreeRankOne M)
    (a : (pullback s).obj M ≅ (pullback s).obj M) :
    ∃ b : M ≅ M, (pullback s).mapIso b = a := by
  obtain ⟨r, hr, _⟩ := existsUnique_scalarUnit (hM.pullback s) a
  refine ⟨scalarUnitIso M (Units.map f.appTop.hom.toMonoidHom r), ?_⟩
  rw [← hr]
  apply Iso.ext
  change (pullback s).map (scalarEnd M (f.appTop (r : Γ(S, ⊤)))) =
    scalarEnd ((pullback s).obj M) (r : Γ(S, ⊤))
  rw [scalarEnd_pullback]
  congr 1
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
  rfl

include hs in
/-- Any line isomorphism can be corrected to preserve both chosen rigidifications. -/
theorem rigidifiedIso_nonempty {M N : X.Modules} (hM : LocallyFreeRankOne M)
    (ρ : (pullback s).obj M ≅ structureModule S)
    (τ : (pullback s).obj N ≅ structureModule S) (i : M ≅ N) :
    Nonempty (RigidifiedIso s ρ τ) := by
  let d := (pullback s).mapIso i ≪≫ τ
  obtain ⟨b, hb⟩ := exists_iso_pullback_eq f s hs hM (ρ ≪≫ d.symm)
  refine ⟨⟨b ≪≫ i, ?_⟩⟩
  change (pullback s).map (b.hom ≫ i.hom) ≫ τ.hom = ρ.hom
  rw [Functor.map_comp, Category.assoc]
  change ((pullback s).mapIso b).hom ≫ d.hom = ρ.hom
  rw [hb]
  simp

include hs in
/-- Rigidification imposes no additional obstruction on the isomorphism class. -/
theorem rigidifiedIso_nonempty_iff {M N : X.Modules} (hM : LocallyFreeRankOne M)
    (ρ : (pullback s).obj M ≅ structureModule S)
    (τ : (pullback s).obj N ≅ structureModule S) :
    Nonempty (RigidifiedIso s ρ τ) ↔ Nonempty (M ≅ N) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i.val⟩
  · rintro ⟨i⟩
    exact rigidifiedIso_nonempty f s hs hM ρ τ i

include hs in
/-- Constant global functions give a unique rigidified lift of any line isomorphism. -/
theorem existsUnique_rigidifiedIso {M N : X.Modules} (hM : LocallyFreeRankOne M)
    (hf : Function.Surjective f.appTop)
    (ρ : (pullback s).obj M ≅ structureModule S)
    (τ : (pullback s).obj N ≅ structureModule S) (i : M ≅ N) :
    ∃! j : M ≅ N, (pullback s).map j.hom ≫ τ.hom = ρ.hom := by
  obtain ⟨j⟩ := rigidifiedIso_nonempty f s hs hM ρ τ i
  refine ⟨j.val, j.property, fun k hk ↦ ?_⟩
  exact congrArg (fun a : RigidifiedIso s ρ τ ↦ a.val)
    ((rigidifiedIso_subsingleton f s hs hf hM ρ τ).elim ⟨k, hk⟩ j)

end FLT.Mazur.FCurve.LineSheafSectionRigidity
