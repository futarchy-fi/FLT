/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedLineBaseChange

/-!
# Pullback of pointed Picard kernels

Compatible maps of pointed families induce actual group homomorphisms on
normalized Picard classes. Identity and composition are inherited from
sheaf pullback, and normalization commutes with these maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemePicard
open FCurve
variable {X P Q S T U : Scheme.{u}}
  (e : S ⟶ X) (d : T ⟶ P) (p : P ⟶ X) (g : T ⟶ S)
  (hp : d ≫ p = g ≫ e)

/-- Actual Picard pullback restricts to the kernels defined by compatible sections. -/
def pointedKernelPullback : (pullback e).ker →* (pullback d).ker where
  toFun c := ⟨pullback p c.val, by
    change pullback d (pullback p c.val) = 1
    rw [← pullback_comp, hp, pullback_comp]
    have hc : pullback e c.val = 1 := c.property
    rw [hc, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

/-- The restricted map keeps the original Picard pullback of the class. -/
lemma pointedKernelPullback_val (c : (pullback e).ker) :
    (pointedKernelPullback e d p g hp c).val = pullback p c.val := rfl

/-- Identity family maps act identically on normalized classes. -/
lemma pointedKernelPullback_id (c : (pullback e).ker) :
    pointedKernelPullback e e (𝟙 X) (𝟙 S) (by simp) c = c :=
  Subtype.ext (pullback_id c.val)

/-- Composition holds for the full normalized class, independent of proof choices. -/
lemma pointedKernelPullback_comp (b : U ⟶ Q) (r : Q ⟶ P) (k : U ⟶ T)
    (hr : b ≫ r = k ≫ d) (c : (pullback e).ker) :
    pointedKernelPullback d b r k hr (pointedKernelPullback e d p g hp c) =
      pointedKernelPullback e b (r ≫ p) (k ≫ g)
        (by rw [← Category.assoc, hr, Category.assoc, hp, Category.assoc]) c :=
  Subtype.ext (pullback_comp r p c.val).symm

include hp in
/-- Normalization commutes with a compatible pointed family map on every Picard class. -/
theorem normalize_pointedSquare (f : X ⟶ S) (q : P ⟶ T) (hf : p ≫ f = q ≫ g)
    (c : Pic X) : pullback p (normalize f e c) = normalize q d (pullback p c) := by
  induction c using inductionOn with
  | h L hL => exact pointNormalizedLine_baseChange_class f e q d p g hf hp L hL

/-- The normalization into the kernel commutes with the actual restricted pullback. -/
theorem normalizeToKernel_pullback (f : X ⟶ S) (q : P ⟶ T)
    (he : e ≫ f = 𝟙 S) (hd : d ≫ q = 𝟙 T) (hf : p ≫ f = q ≫ g) (c : Pic X) :
    pointedKernelPullback e d p g hp (normalizeToKernel f e he c) =
      normalizeToKernel q d hd (pullback p c) :=
  Subtype.ext (normalize_pointedSquare e d p g hp f q hf c)

end FLT.Mazur.SchemePicard
