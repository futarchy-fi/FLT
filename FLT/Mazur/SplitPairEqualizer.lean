/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RingEqualizerDescent
public import FLT.Mazur.RelativePinchingLocalDescent

/-!
# Finite pinching of two augmented affine rings

Two affine branches with split evaluations to a field have a finite
normalization over their matching-pair ring. No polynomial presentation is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SplitPairEqualizer
set_option backward.isDefEq.respectTransparency false
variable {K C D : Type*} [Field K] [CommRing C] [CommRing D]
  (f : C →+* K) (g : D →+* K) (l : K →+* C) (r : K →+* D)
  (hl : f.comp l = RingHom.id K) (hr : g.comp r = RingHom.id K)

/-- Evaluation on the first affine summand. -/
def leftEval : C × D →+* K := f.comp (RingHom.fst _ _)
/-- Evaluation on the second affine summand. -/
def rightEval : C × D →+* K := g.comp (RingHom.snd _ _)
/-- Pairs of functions with equal values at the marked points. -/
abbrev E := (leftEval f (D := D)).eqLocus (rightEval g (C := C))

include hl hr in
/-- Constants give a section of the evaluation on matching pairs. -/
theorem evaluation_surjective :
    Function.Surjective ((leftEval f).comp (E f g).subtype) := by
  intro x
  refine ⟨⟨(l x, r x), ?_⟩, ?_⟩
  · change f (l x) = g (r x)
    exact (RingHom.congr_fun hl x).trans (RingHom.congr_fun hr x).symm
  · exact RingHom.congr_fun hl x

include hl hr in
/-- The normalization is generated as a module by one and a branch idempotent. -/
theorem span_pair : Submodule.span (E f g) ({1, (1, 0)} : Set (C × D)) = ⊤ := by
  apply top_unique
  intro p _
  let t := f p.1 - g p.2
  let c : E f g := ⟨(l t, r t), by
    change f (l t) = g (r t)
    exact (RingHom.congr_fun hl t).trans (RingHom.congr_fun hr t).symm⟩
  let q : E f g := ⟨(p.1 - l t, p.2), by
    change f (p.1 - l t) = g p.2
    rw [map_sub, show f (l t) = t from RingHom.congr_fun hl t]
    exact sub_sub_cancel _ _⟩
  have h : p = q • (1 : C × D) + c • (1, 0) := by
    change p = (p.1 - l t, p.2) * 1 + (l t, r t) * (1, 0)
    ext <;> simp
  rw [h]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

include hl hr in
/-- Finiteness of the actual inclusion into the product of the two branch rings. -/
theorem inclusion_finite : (E f g).subtype.Finite := by
  let _ : Module.Finite (E f g) (C × D) := by
    classical
    apply Module.Finite.of_fg_top
    exact ⟨{1, (1, 0)}, by simpa using span_pair f g l r hl hr⟩
  change (algebraMap (E f g) (C × D)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

end FLT.Mazur.SplitPairEqualizer
