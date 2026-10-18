/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingCyclicIdeal
public import FLT.Mazur.FaithfulMarkingSectionRelabeling

/-!
# Finite relabeling retains the smoothing's whole cyclic subgroup ideal

Relabeling a faithful cyclic parameter permutes its original sections and
preserves the entire closed subgroup in the actual proper smoothing family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R) (n : ℕ) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of R))
  (f : Over.mk g ⟶ relativeCyclicParameter t n) (e : MulAut (Multiplicative (ZMod n)))

/-- The relabeled faithful cyclic test over the unchanged original coefficient base. -/
def relativeCyclicRelabeledTest : Over.mk g ⟶ relativeCyclicParameter t n :=
  faithfulRelabeledTest (relativeGroup t).X (Multiplicative (ZMod n)) g f e

local notation "f'" => relativeCyclicRelabeledTest t n g f e

/-- Relabeling preserves the actual full subgroup ideal on the original smoothing test. -/
theorem relativeCyclicIdeal_relabel :
    relativeCyclicIdeal t n g (f') = relativeCyclicIdeal t n g f := by
  rw [relativeCyclicIdeal_product, relativeCyclicIdeal_product]
  have hs (i : ZMod n) : relativeCyclicMarking t n g (f') (.ofAdd i) =
      relativeCyclicMarking t n g f (e.symm (.ofAdd i)) :=
    faithfulRelabeledTest_section (relativeGroup t).X (Multiplicative (ZMod n)) g f e _
  simp only [hs]
  let d : ZMod n ≃ ZMod n := (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n)) |>.trans
    (e.symm.toEquiv.trans Multiplicative.toAdd)
  exact Equiv.prod_comp d (fun i : ZMod n ↦
    (relativeCyclicMarking t n g f (.ofAdd i) ≫ relativeTestInclusion t g).left.ker)

/-- The closed embeddings have exactly the same scheme-theoretic image after relabeling. -/
theorem relativeCyclicCurveMap_relabel_kernel :
    (relativeCyclicCurveMap t n g (f')).left.ker =
      (relativeCyclicCurveMap t n g f).left.ker :=
  relativeCyclicIdeal_relabel t n g f e

end FLT.Mazur.OneGonSmoothing
