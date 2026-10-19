/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite fibers descend along a surjective Cartesian base change

Each original point fiber is the image of a geometric point fiber. Finiteness
therefore descends on points; for a finite type map this proves quasi-finiteness,
and for a proper map it proves finiteness of the whole morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteFiberSurjectiveDescent

universe u
variable {P X Y S : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
  (H : IsPullback a b f g) [Surjective g] [LocallyQuasiFinite b] [QuasiCompact b]

include H in
/-- Every original point fiber is covered by a finite fiber of the actual pullback. -/
theorem finite_preimage_singleton (s : S) : (f ⁻¹' {s}).Finite := by
  obtain ⟨y, rfl⟩ := g.surjective s
  apply ((b.finite_preimage_singleton y).image a).subset
  intro x hx
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback H x y hx
  exact ⟨z, hz₂, hz₁⟩

include H in
/-- Quasi-finiteness descends for a finite type original morphism. -/
theorem locallyQuasiFinite [LocallyOfFiniteType f] : LocallyQuasiFinite f :=
  LocallyQuasiFinite.of_finite_preimage_singleton f (finite_preimage_singleton H)

include H in
/-- A proper original morphism is finite when its whole surjective pullback is finite. -/
theorem isFinite [IsProper f] : IsFinite f := by
  let _ := locallyQuasiFinite H
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end FLT.Mazur.FiniteFiberSurjectiveDescent
