/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnitySubgroupGenerator
public import FLT.Mazur.RootsOfUnityGroupBaseChange
public import FLT.Mazur.IntegralCyclotomicAffineCover

/-!
# Fppf cyclicity of original roots subgroups

The cyclotomic tensor cover supplies a generator on the actual subgroup
pullback. The character comparison preserves its group law, and the full
intrinsic product proves cyclicity without replacing the ambient family.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

set_option backward.isDefEq.respectTransparency false

open CharacterSchemeBaseChange IntegralCyclotomicAffineCover

variable {R : Type} [CommRing R] {E : GeneralizedEllipticCurve (Spec (.of R))}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (e : RootsOfUnityScheme.model R n ≅ H.carrier) [IsMonHom e.hom]

/-- Roots coordinates on the actual original subgroup after a coefficient extension. -/
def rootsBaseChangeIso (A : Type) [CommRing A] [Algebra R A] :
    RootsOfUnityScheme.model A n ≅ (H.baseChange (baseMap R A)).carrier :=
  RootsOfUnityArithmeticPullback.comparison R A n ≪≫ (Over.pullback (baseMap R A)).mapIso e

instance rootsBaseChangeIso_isMonHom (A : Type) [CommRing A] [Algebra R A] :
    IsMonHom (H.rootsBaseChangeIso e A).hom := by
  dsimp only [rootsBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom]
  infer_instance

/-- The cyclotomic root on the genuine original subgroup pullback is a Cartier generator. -/
theorem roots_cover_isCartierGenerator [SmoothOfRelativeDimension 1 E.group.hom] :
    (H.baseChange (baseMap R (Algebra R n))).IsCartierGenerator
      ((H.baseChange (baseMap R (Algebra R n))).rootsGenerator
        (H.rootsBaseChangeIso e (Algebra R n)) (specialization R n)) := by
  let _ : SmoothOfRelativeDimension 1
      (E.baseChange (baseMap R (Algebra R n))).group.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact (H.baseChange (baseMap R (Algebra R n))).rootsGenerator_isCartierGenerator
    (H.rootsBaseChangeIso e (Algebra R n)) (specialization R n)

include e in
/-- Any finite subgroup with the roots group as its carrier is cyclic on the original curve. -/
theorem isCyclic_of_rootsIso [SmoothOfRelativeDimension 1 E.group.hom] : H.IsCyclic := by
  obtain ⟨hf, hs, hl⟩ := fppf R n
  exact ⟨_, baseMap R (Algebra R n), hf, hs, hl, _, H.roots_cover_isCartierGenerator e⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
