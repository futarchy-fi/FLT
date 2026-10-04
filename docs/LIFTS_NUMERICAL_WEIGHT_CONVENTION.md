# Numerical weight convention and the normalized BDJ table

Use odd primes only. `NormalizedRecipe` encodes the disjoint table in the
proof of BDJ Theorem 3.17, pp. 29–30,
<https://arxiv.org/pdf/0810.2106>. It returns labels
`V(a,b) = det^a ⊗ Sym^(b-1)`, with a modulo p-1 and 1 <= b <= p.
Its input is branch data, not a representation together with an asserted
weight. Arithmetic extraction of the branch remains a separate theorem.

The numerical convention for this project is the least **classical** weight
k >= 2 for the untwisted representation. It excludes Katz weight one.
More precisely, given the full independent BDJ set W(rho), set

    k_min(rho) = min { k >= 2 : some Jordan–Hölder constituent of
                      Sym^(k-2)(Fbar_p^2) belongs to W(rho) }.

This specifies the convention; it is not yet a Lean definition or an assertion
of modularity. Existence of the minimum and the comparison with Serre's
numerical recipe must be proved before an API named `serreWeight` is used.
The comparison uses actual GL_2(F_p) modules and their composition factors;
no caller may supply a table of asserted evaluations as a hypothesis.

BDJ §2, especially Proposition 2.5 and Corollary 2.11, explains passage between
coefficient modules and classical weights; the proof of Theorem 3.17 uses
`V(0,b)` for classical weight b+1 and determinant twisting for cyclotomic
twists. Ribet–Stein, Chapter 2,
<https://wstein.org/papers/serre/ribet-stein.pdf>, explicitly distinguishes its
convention from the weight-one refinement and restricts its ordinary
calculation to a trivial lower inertial character (§2.2.4). That restricted
calculation is not a rule for all determinant twists.

Consequences at the specification level:

- Weight 2 means `V(0,1)` belongs to the full set, since Sym^0 is trivial.
- Scalar unramified inertia has normalized exponent p-1, not exponent zero;
  its table entry is `V(0,p-1)`, corresponding to classical weight p.
- The exceptional cyclotomic tres branch has only `V(0,p)`; the peu branch
  also contains `V(0,1)`. This distinguishes p+1 from 2 without defining
  finite flatness by the desired weight.
- Determinant twisting changes the first label modulo p-1. It is not legitimate
  to minimize b+1 while dropping that first label. Twisting a representation
  to normalize it is different from computing its original numerical weight.
- The p=3 split exponent-one branch has four labels and must precede the
  p-2 branch; `NormalizedRecipe` implements that order and proves bounds.

Remaining S0 work: extract whole-local splitting, normalized inertia characters
and the independent extension class from actual representations; establish
independence of normalization and full twist/coefficient compatibility; develop
the symmetric-power composition-factor comparison above. W42 proves actual
ordinary class basis/twist invariance but does not alone identify all these
branch inputs. No S1 evaluation is claimed or dispatched by this specification.
