# Ordinary local inputs: source contracts after W42

Checked at 2026-10-04T03:25:27Z. This is a source specification, not a
Serre-weight implementation or a
finite-flat/unit theorem. Recheck with `python3 Scratch/LiftsW42/audit-next.py`;
that command records its time, source hashes and the actual searches. Saved
external sources and their URLs/hashes are in `Scratch/LiftsW42/sources.json`.

## The proved representation input

`OrdinaryFiltration ρ α β` is an exact sequence of the actual representations
`0 → k(α) → V → k(β) → 0`: its fields are linear maps, exactness,
injectivity/surjectivity and equivariance. There is no class, comparison
isomorphism, unit witness, cup evaluation or lifting conclusion among its fields.
Applying Hom from the quotient line constructs an equivariant coefficient
injection. A vector above one constructs a section; its translated difference
constructs the actual continuous Hom-valued cocycle. The class is independent
of the section. `galoisClass` discharges continuity from the existing `GaloisRep`.

`ordinaryRepresentationPeuRamified_iff_unit` applies W41 to this extracted class.
Its hypothesis is equality of the **whole local Hom character** with the
scalar-extended cyclotomic character, not just equality on inertia. Rescaling
sub-line/quotient bases by a/b transports the class by b/a; a simultaneous scalar
twist transports it by the identity on Hom. These formulas, and unit invariance
for the actual changed filtrations, are proved in W42.

This covers filtrations supplied as exact two-line sequences. Automatic detection
of an ordinary filtration from an arbitrary finite-flat model is separate work.

## Finite-flat arithmetic: the integral parameter cannot be assumed

Source: Stacks Project, Kummer theory, Section 59.28, especially **Lemma 59.28.3
(tag 040N)** and its following fppf cohomology sequence:
<https://stacks.math.columbia.edu/tag/03PK>.
The lemma holds without inverting p. The preceding étale lemma 03PL requires p
invertible and must not be used on the integers at p.

For an actual commutative p-torsion extension of the constant Z/p group by μp
over a DVR O, the fibre over 1 is a μp-torsor for the fppf topology. The fppf
Kummer sequence gives
`Oˣ/(Oˣ)^p → H¹_fppf(O, μp) → Pic(O)[p]`.
Since invertible modules over a local ring are free, `Pic(O)=0`. Thus the fibre
has an integral-unit parameter. Restriction to the fraction field must then be
proved to give the same root-ratio class as `galoisClass`, with its specified
injection and quotient normalization. This is a derived unit witness, never
an extra field of the finite-flat model.

Source: Buzzard–Diamond–Jarvis, *On Serre's conjecture for mod ℓ Galois
representations over totally real fields*, **Remark 3.11**, pp. 25–26 of
<https://arxiv.org/pdf/0810.2106>. It identifies the cyclotomic finite/crystalline
extension subspace with `Oˣ ⊗ F̄p`, hence the peu-ramified classes. This is an
independent arithmetic comparison, not a license to define finite flatness or
the Serre recipe by the desired unit conclusion.

| Bounded next leaf | Required construction; readiness |
|---|---|
| R1a1 | From the generic invariant line take its flat schematic closure and quotient, preserving the actual coefficient action. Existing `RaynaudFiltrationLayers` and integral subquotient APIs are starting points; source/interface review before coding. |
| R1a2 | Identify those **constructed** rank-one models as the needed multiplicative and étale character twists. Generic character equality alone does not give an integral isomorphism. Blocked on the rank-one model comparison. |
| R1b1 | Construct the quotient fibre over 1 as a μp-torsor with its torsor action and faithfully flat cover. Restrict initially to an actual μp/constant-Z/p extension. No torsor witness may stand in for this construction. |
| R1b2 | Prove the local-ring integral Kummer parameter theorem for that torsor, using the fppf sequence/Picard vanishing or an explicit descent proof. The current field-Kummer API is insufficient. |
| R1b3 | Prove generic-fibre compatibility with W42's normalized difference cocycle; then W41 gives peu ramification. Depends on R1b2. |
| R1c | Descend unramified twists and extend residual coefficients while retaining their action. A coefficient basis cannot replace this arithmetic descent. Depends on R1a2/R1b3. |

Each proof module must stay at most 200 lines; these are contracts to refine,
not claims that the entire integral theory fits into six short proofs.

## Independent odd-prime weight recipe

Use BDJ **Theorem 3.17 and its proof**, pp. 29–30, with §3's definition of the
extension subspaces, as the complete normalized local **weight-set** specification.
Write `V(a,b)=det^a ⊗ Sym^(b−1)(F̄p²)`; a is modulo p−1 and `1≤b≤p`.
The table below is for odd p, matching the lifting endpoint. Twisting is
handled by BDJ Proposition 3.15(1). The modularity assertion of Theorem 3.17
is not an input available in Lean; only its explicit recipe is being specified.

After a cyclotomic twist the niveau-two case has inertia characters
`ω₂^b, ω₂^(pb)` with `1≤b≤p−1`. Its set is
`{V(0,b), V(b−1,p+1−b)}`. The reducible case has inertia form
`(ω^b, *; 0, 1)` with `1≤b≤p−1`, and actual local diagonal characters χ₁,χ₂.
Use the following ordered, disjoint branches:

| Reducible local case | Weight set |
|---|---|
| `1<b<p−1`, nonsplit | `{V(0,b)}` |
| `1<b<p−2`, split | `{V(0,b), V(b,p−1−b)}` |
| `b=p−2`, p>3, split | `{V(0,p−2), V(p−2,p), V(p−2,1)}` |
| `b=p−1` (including scalar inertia, split or nonsplit) | `{V(0,p−1)}` |
| `b=1`, χ₁/χ₂=ω on the whole local group, tres ramified | `{V(0,p)}` |
| `b=1`, p>3, split | `{V(0,p), V(0,1), V(1,p−2)}` |
| `b=1`, p=3, split | `{V(0,3), V(0,1), V(1,3), V(1,1)}` |
| Remaining `b=1` nonsplit cases | `{V(0,p), V(0,1)}` |

Splitting here is splitting over the full local decomposition group. The
exceptional peu/tres branch uses the independent extension-class subspace
(cup annihilation after W41/W42), not finite-flatness as its definition.
The last branch includes χ₁/χ₂ unramified-twisted cyclotomic but unequal to ω;
W42's cyclotomic Hom hypothesis must not be silently weakened to cover it.

In the general definition, BDJ modifies the crystalline subspace in two
exceptional cases: cyclotomic ratio with all b=p and J=S gives all H¹; trivial
ratio and J≠S adds the unramified line. These exceptions explain why a recipe
using just two inertia eigenvalues or just one cup predicate is incomplete.

This weight set is **not itself a definition of the numerical Serre weight**
`serreWeight p ρ` sketched in older ledger tables. A separate specification must
relate it to the minimal classical weight ≥2, including determinant twists and
scalar cases, before that numerical API is implemented. In particular the
pedagogical formula `1+pr+q` at r=q=0 gives 1 and cannot be used uncorrected.
Ribet–Stein, *Lectures on Serre's conjectures*, §§2.2–2.3
(<https://wstein.org/papers/serre/ribet-stein.pdf>) explains the weight-2 versus
p+1 distinction; its restricted discussion does not replace the full table.

| Next specification leaf | Acceptance |
|---|---|
| S0a1 | Encode/check the finite odd-prime normalized branch data above, including p=3 overlap and scalar inertia, without attaching arithmetic truth fields. Ready as specification work only. |
| S0a2 | Identify the actual invariant-line/splitting, inertia-character and extension-class inputs; prove invariance under basis change/twist using W42, rather than accepting equivalences as inputs. |
| S0a3 | Source-match the numerical-weight convention and its equivalence with the required weight-set membership. Needed before the historical S1 numerical evaluation task. |

No Serre-weight evaluation or arbitrary-prime Raynaud classification is dispatched
by this document. The finite-flat implication still needs R1/R2 even after a
weight recipe is defined.
