/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
public import FLT.Mazur.WeierstrassSuccessiveShearComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Whole tensor lines in the actual retained equations

The inverse coefficient shear identifies the original full tensor-line maps
with the middle-line immersions in the retained atlas, before any gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q (Data.b6 d)
variable (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "e" => coefficientShearMiddleEquiv W (π ^ (start + i.val)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4
local notation "h2" => coefficientShear_a₂_zero W S r hr

local notation "E" => coefficientShearRetainedEquationIso data S r t ht i hs hp h3 h4
local notation "ci" => successiveCoefficientShearIso W (π ^ (start + i.val)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r
variable (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "line" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (tensorShearLineMap W (π ^ (start + i.val)) π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr v hv)))

/-- The complete original tensor line is the actual retained middle line. -/
theorem coefficientShearRetainedEquationIso_tensor_line :
    line ≫ (ci).inv = middleLineImmersion U c h2 v hv ≫ (E).hom := by
  apply (cancel_mono (ci).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
