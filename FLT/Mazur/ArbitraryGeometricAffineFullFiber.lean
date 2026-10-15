/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricAllLiftTranslations
public import FLT.Mazur.AffineHilbertConstructedGeometricRetention

/-!+# Constructed original affine full fibers through arbitrary geometric classes

All-independent-lift translations supply the acyclicity needed for original
affine retention. A finite family uses one degree and one translation test;
its classes need not extend to the original base or to that test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))

include hL in
/-- Every prescribed geometric class lies in a constructed original affine full envelope fiber. -/
theorem exists_finite_geometric_affine_full_fibers {n : ℕ}
    (s : Fin n → (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : Fin n → (relativeFppfSheaf f).obj.obj (op V)),
      IsAffine V.left ∧ Etale V.hom ∧ ∀ i,
      ∃ (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
        (b : Over.mk t ⟶ A), IsAffine A.left ∧ ∃ hk : IsOpenImmersion k.left,
        let _ := hk
        (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V (c i) k) = s i ∧
        b.left η ∈ fullEnvelopeLocus f hL d V (c i) k := by
  obtain ⟨d, V, c, v, hV, he, hv⟩ :=
    exists_arbitrary_geometric_all_lift_translations f hL t s
  let _ := hV
  let _ := he
  refine ⟨d, V, c, hV, he, fun i ↦ ?_⟩
  obtain ⟨A, k, b, hA, hk, _, hb, hf⟩ :=
    exists_affine_full_fiber_of_geometric_acyclicity f hL d V (c i) (s i) v
      (fun w ↦ hv w i)
  exact ⟨A, k, b, hA, hk, hb, hf⟩

include hL in
/-- A single arbitrary original class is retained, with no initial chart or fullness premise. -/
theorem exists_arbitrary_geometric_affine_full_fiber
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A), IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left, let _ := hk
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      b.left η ∈ fullEnvelopeLocus f hL d V c k := by
  obtain ⟨d, V, c, hV, he, h⟩ :=
    exists_finite_geometric_affine_full_fibers f hL t (fun _ : Fin 1 ↦ s)
  obtain ⟨A, k, b, hA, hk, hb, hf⟩ := h 0
  exact ⟨d, V, c 0, A, k, b, hV, he, hA, hk, hb, hf⟩

end FLT.Mazur.HilbertChart.AffineRestriction
