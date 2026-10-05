/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.DeSmitLenstra.TraceSpecialization

/-!
# Morphisms of universal trace coefficients are determined by traces

The density argument applies to arbitrary proartinian targets and requires
no Noetherianity of the trace source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory IsLocalRing
namespace Deformation

universe u
variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (n : Type) [Fintype n] [DecidableEq n]
  (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))

omit [TotallyDisconnectedSpace G] in
/-- Continuous coefficient maps agreeing on universal traces are equal. -/
theorem universalTraceMorphism_ext (S : ProartinianCat O)
    (f h : universalTraceRingObject O G n rho ⟶ S)
    (he : ∀ g : G,
      f.hom ⟨(profiniteUniversalMatrix O G n rho g).trace,
        universalTrace_mem O G n rho g⟩ =
      h.hom ⟨(profiniteUniversalMatrix O G n rho g).trace,
        universalTrace_mem O G n rho g⟩) : f = h := by
  let A : Subalgebra O (ProfiniteFramedLimit O G n rho) :=
    Algebra.adjoin O (Set.range fun g : G ↦ (profiniteUniversalMatrix O G n rho g).trace)
  let inc : A →ₐ[O] UniversalTraceRing O G n rho :=
    Subalgebra.inclusion (Subalgebra.le_topologicalClosure A)
  have hA : f.hom.toAlgHom.comp inc = h.hom.toAlgHom.comp inc := by
    apply AlgHom.adjoin_ext
    rintro x ⟨g, rfl⟩
    exact he g
  have hdense : DenseRange (Set.inclusion (Subalgebra.le_topologicalClosure A)) := by
    rw [denseRange_inclusion_iff (Subalgebra.le_topologicalClosure A)]
    rw [Subalgebra.topologicalClosure_coe]
  apply ProartinianCat.hom_ext
  apply DFunLike.ext _ _
  intro x
  apply congr_fun (hdense.equalizer f.hom.cont h.hom.cont ?_) x
  funext a
  exact DFunLike.congr_fun hA a

end Deformation
