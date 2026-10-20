/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TorusSubgroupArithmeticComparison
public import FLT.Mazur.TorusCyclotomicGenerator
public import FLT.Mazur.CyclotomicCoverRootSection

/-!
# Arithmetic cyclicity of the original toric subgroup

The finite faithfully flat cyclotomic cover carries an actual Cartier generator
of the original subgroup pullback. Its full orbit ideal, including multiplicities,
descends to cyclicity over every coefficient ring without inverting the order.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GeneralizedEllipticCurve

open CharacterSchemeBaseChange IntegralCyclotomicAffineCover

variable {R : Type} [CommRing R] (E : GeneralizedEllipticCurve (Spec (.of R)))
  (e : MultiplicativeGroupScheme.gm R ≅ E.group) [IsMonHom e.hom]
  (n : ℕ) [NeZero n]

/-- The explicit cyclotomic section generates the actual original subgroup pullback. -/
theorem torusRootsOfUnitySubgroup_cover_generator :
    ((E.torusRootsOfUnitySubgroup e n).baseChange (baseMap R (Algebra R n))).IsCartierGenerator
      (CyclotomicCoverRootSection.rootSection R n) := by
  exact E.arithmeticSubgroup_generator_transport e (Algebra R n) n
    ((E.baseChange (baseMap R (Algebra R n))).torusCyclotomicGenerator_cartier
      (E.arithmeticTorusIso e (Algebra R n)) n (specialization R n))

/-- Roots of unity in any actual toric generalized curve form a cyclic finite subgroup. -/
theorem torusRootsOfUnitySubgroup_isCyclic : (E.torusRootsOfUnitySubgroup e n).IsCyclic := by
  obtain ⟨hf, hs, hl⟩ := fppf R n
  let _ := hf
  let _ := hs
  let _ := hl
  exact FiniteSubgroup.IsCyclic.of_baseChange _ (baseMap R (Algebra R n))
    ((E.torusRootsOfUnitySubgroup_cover_generator e n).isCyclic _)

/-- Every scheme test retains cyclicity of the original toric subgroup. -/
theorem torusRootsOfUnitySubgroup_baseChange_isCyclic {T : Scheme}
    (f : T ⟶ Spec (.of R)) : ((E.torusRootsOfUnitySubgroup e n).baseChange f).IsCyclic :=
  (E.torusRootsOfUnitySubgroup_isCyclic e n).baseChange _ f

end FLT.Mazur.GeneralizedEllipticCurve
