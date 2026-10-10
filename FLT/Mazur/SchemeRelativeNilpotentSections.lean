/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeConnectedFiberSections
public import FLT.Mazur.SchemeNilpotentSectionDetection

/-!
# The infinitesimal obstruction to relative constant functions

For a pointed proper family with connected reduced geometric fibers, every
function differs from its section value by a nilpotent, even over a nonreduced
base. The actual evaluation kernel is a nil ideal. Its vanishing, still to be
proved for flat families, is precisely the missing relative comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelativeNilpotentSections
variable {X S : Scheme.{0}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
include hs

/-- Evaluation of a pulled-back base function recovers that base function. -/
lemma evaluation_pullback (a : Γ(S, ⊤)) : s.appTop (f.appTop a) = a := by
  have h : f.appTop ≫ s.appTop = 𝟙 Γ(S, ⊤) := by
    rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
  exact ConcreteCategory.congr_hom h a

/-- The difference between a function and its section value lies in the actual kernel. -/
lemma sub_evaluation_mem_ker (a : Γ(X, ⊤)) :
    a - f.appTop (s.appTop a) ∈ RingHom.ker s.appTop.hom := by
  change s.appTop (a - f.appTop (s.appTop a)) = 0
  rw [map_sub, evaluation_pullback f s hs, sub_self]

variable [IsProper f] [GeometricallyConnected f] [GeometricallyReduced f]
  [CompactSpace X]

/-- A function differs from its actual section value by a nilpotent. -/
lemma sub_evaluation_isNilpotent (a : Γ(X, ⊤)) :
    IsNilpotent (a - f.appTop (s.appTop a)) := by
  apply SchemeNilpotentSectionDetection.isNilpotent_sub_of_residue_pullback
  intro x
  have hpoint : (X.fromSpecResidueField x ≫ f ≫ s) ≫ f =
      X.fromSpecResidueField x ≫ f := by
    simp only [Category.assoc, hs, Category.comp_id]
  have h := SchemeConnectedFiberSections.appTop_eq_of_same_fiber f
    (X.fromSpecResidueField x ≫ f ≫ s) (X.fromSpecResidueField x) hpoint
  change (X.fromSpecResidueField x ≫ f ≫ s).appTop =
    (X.fromSpecResidueField x).appTop at h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact (ConcreteCategory.congr_hom h a).symm

include f in
/-- Every element of the section-evaluation kernel is nilpotent. -/
lemma evaluation_ker_le_nilradical :
    RingHom.ker s.appTop.hom ≤ nilradical Γ(X, ⊤) := by
  intro a ha
  have h := sub_evaluation_isNilpotent f s hs a
  have hz : s.appTop a = 0 := ha
  simpa only [hz, map_zero, sub_zero, mem_nilradical] using h

/-- Every function has its specified scalar part and a nilpotent evaluation-zero part. -/
lemma exists_evaluation_decomposition (a : Γ(X, ⊤)) :
    ∃ n : RingHom.ker s.appTop.hom,
      a = f.appTop (s.appTop a) + n.val ∧ IsNilpotent n.val := by
  refine ⟨⟨a - f.appTop (s.appTop a), sub_evaluation_mem_ker f s hs a⟩, ?_,
    sub_evaluation_isNilpotent f s hs a⟩
  dsimp
  abel

end FLT.Mazur.SchemeRelativeNilpotentSections
