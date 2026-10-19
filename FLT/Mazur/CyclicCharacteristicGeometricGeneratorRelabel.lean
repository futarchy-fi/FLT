/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleGeometricGeneratorRelabel
public import FLT.Mazur.CyclicCharacteristicNormalizedGenerator
public import FLT.Mazur.CyclicCharacteristicProductParameterGroupoid

/-!
# Cyclic relabeling along actual geometric characteristic arrows

Every geometric point of the full comparison scheme supplies an automorphism
of the original cyclic label group matching all generator powers. This holds
between either pair of characteristic charts and retains the given compatible
isomorphism. Auxiliary-frame alignment is still needed for parameter equality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
variable (n : ℕ) [NeZero n] {K : Type} [Field K] [IsAlgClosed K]
  {b c : Bool} (q : Spec (.of K) ⟶ normalizedLocus n b)
  (r : Spec (.of K) ⟶ normalizedLocus n c)

/-- Every original compatible geometric comparison matches all cyclic labels after relabeling. -/
theorem compatible_geometric_generator_relabel
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q)
      ((normalizedSubgroup n c).baseChange r)) :
    ∃ e : MulAut (Multiplicative (ZMod n)), ∀ i,
      (pullSection q (normalizedGenerator n b) ^ (e i).toAdd.val) ≫ a.subgroup.hom =
        pullSection r (normalizedGenerator n c) ^ i.toAdd.val :=
  a.exists_geometric_generator_relabel
    (normalizedGenerator_pull_cartier n b q) (normalizedGenerator_pull_cartier n c r)

/-- Apply the generator comparison to the actual original full comparison scheme. -/
theorem productArrow_geometric_generator_relabel (a : ProductArrow n q r) :
    ∃ e : MulAut (Multiplicative (ZMod n)), ∀ i,
      (pullSection q (normalizedGenerator n b) ^ (e i).toAdd.val) ≫
        (productCompatibleTestComparison n b c q r a).subgroup.hom =
          pullSection r (normalizedGenerator n c) ^ i.toAdd.val :=
  compatible_geometric_generator_relabel n q r (productCompatibleTestComparison n b c q r a)

/-- The automorphism extends to the existing common finite relabeling group. -/
theorem productArrow_geometric_common_cyclic_relabel (a : ProductArrow n q r) :
    ∃ e : RelabelGroup n, ∀ i,
      (pullSection q (normalizedGenerator n b) ^ (e.2.2.symm i).toAdd.val) ≫
        (productCompatibleTestComparison n b c q r a).subgroup.hom =
          pullSection r (normalizedGenerator n c) ^ i.toAdd.val := by
  obtain ⟨e, he⟩ := productArrow_geometric_generator_relabel n q r a
  exact ⟨⟨1, 1, e.symm⟩, he⟩

end FLT.Mazur.CyclicCharacteristicAtlas
