/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialEquationDescent
public import FLT.Mazur.WeierstrassIncidenceShearConicCoefficient

/-!
# The whole original tensor conic in the actual initial equation

The inverse coefficient shear preserves the entire conic immersion and every
original function, before making any restriction to a puncture.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (d).b6
local notation "E" => coefficientShearInitialEquationIso data S r j hj hs h3 h4 hr
local notation "ci" => incidenceCoefficientShearIso W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r
local notation "F" => tensorShearInitialConicMap W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r hs h3 h4 hr

/-- The original full tensor conic agrees with the normal conic in the actual initial chart. -/
@[reassoc] theorem coefficientShearInitialEquationIso_tensor_conic :
    Spec.map (CommRingCat.ofHom (F).toRingHom) ≫ (ci).inv =
      fiberConicImmersion a c ≫ (E).hom := by
  apply (cancel_mono (ci).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
