/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FlatFramedChange
public import FLT.Deformations.RepresentationTheory.FlatCofinal
public import FLT.Deformations.IsProartinian

/-!
# Descent of finite-flat reductions along coefficient embeddings

The subspace topology makes pulled-back open ideals cofinal. Each reduction
embeds into a finite-flat target reduction, so schematic closure supplies a
model. Compactness supplies the subspace topology for continuous injections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField
namespace FramedGaloisRep
variable {K : Type} [Field K] [NumberField K]
  {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLocalRing A] [IsLocalRing B] [IsLinearTopology B B]
  {n : Type} [Fintype n] [DecidableEq n]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : FramedGaloisRep K A n)
  (f : A →+* B) (hf : Continuous f)

/-- The induced coefficient topology suffices to descend all finite-flat reductions. -/
theorem isFlatAt_of_isInducing (hind : Topology.IsInducing f)
    (h : (ρ.baseChange f hf).IsFlatAt v) : ρ.IsFlatAt v := by
  constructor
  intro I hI
  have hb := hind.basis_nhds (x := 0)
    (show (nhds (f 0)).HasBasis (fun J : Ideal B ↦ IsOpen (J : Set B))
      (fun J ↦ (J : Set B)) by
        rw [map_zero]
        exact IsLinearTopology.hasBasis_open_ideal)
  obtain ⟨J, hJ, hJI⟩ := hb.mem_iff.mp (hI.mem_nhds I.zero_mem)
  let F := (Ideal.Quotient.mk J).comp f
  have hF : Continuous F := continuous_quot_mk.comp hf
  have hm := (hasFlatProlongationAt_baseChange_iff v (ρ.baseChange f hf)).mp
    (h.cond J hJ)
  have he : (ρ.baseChange f hf).baseChange (Ideal.Quotient.mk J) continuous_quot_mk =
      ρ.baseChange F hF := by
    apply FramedGaloisRep.GL.injective
    ext g i j
    simp only [FramedGaloisRep.baseChange_GL]
    rfl
  have hk : RingHom.ker F ≤ I := by
    intro a ha
    apply hJI
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
  exact GaloisRep.hasFlatProlongationAt_quotient_of_le v ρ hk
    (hasFlatProlongationAt_kernel v ρ F hF (he ▸ hm))

/-- A continuous injection from compact coefficients reflects finite flatness.
No flatness or finiteness of the coefficient-ring extension is required. -/
theorem isFlatAt_of_compact_injective [CompactSpace A] [T2Space B]
    (hinj : Function.Injective f) (h : (ρ.baseChange f hf).IsFlatAt v) :
    ρ.IsFlatAt v :=
  isFlatAt_of_isInducing v ρ f hf (hf.isClosedEmbedding hinj).isEmbedding.isInducing h

end FramedGaloisRep
