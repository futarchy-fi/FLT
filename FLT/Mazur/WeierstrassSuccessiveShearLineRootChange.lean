/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearComponents

/-!
# Full original line maps under change of tangent root

The original three tensor coordinates determine the entire map. Equality of
the unsheared slopes therefore compares the actual lines, including their node origins.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r t : S)
  (hs : algebraMap R S s = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (v w : S)
  (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
  (hw : w * (w + (rootShearCurve (W.map (algebraMap R S)) t).a₁) = 0)

/-- The actual original line map depends on its unsheared slope, over any coefficient ring. -/
theorem tensorShearLineMap_rootChange (hvw : v + r = w + t) :
    tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv =
      tensorShearLineMap W s π b3 b4 b6 S t hs hp h3 h4 ht w hw := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  change tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv
    (tensorCoord W s π b3 b4 b6 S i) =
      tensorShearLineMap W s π b3 b4 b6 S t hs hp h3 h4 ht w hw
        (tensorCoord W s π b3 b4 b6 S i)
  rw [tensorShearLineMap_coord, tensorShearLineMap_coord, hvw]

end FLT.Mazur.WeierstrassSuccessiveX
