# goedel

Native R tools for first-order syntax, exact syntax coding, finite proof checking
and conditional queries about incompleteness. Python and R implement the same
versioned mathematical contract and share independently derived reference cases.
Neither package requires the other at runtime.

```r
library(goedel)
f <- forall("y", predicate("P", list(variable("x"), variable("y"))))
g <- substitute_formula(f, "x", variable("y"))
free_variables(g)                 # "y": substitution avoids capture
alpha_equal(decode(encode(g)), g) # TRUE; code is an exact decimal string

A <- predicate("A"); B <- predicate("B")
answer <- bounded_proof_search(B, list(A, implication(A, B)))
answer$status                    # "ESTABLISHED"
check_proof(answer$witness, list(A, implication(A, B)))$status
```

The finite proof fragment supports assumptions, closed axioms, modus ponens,
conjunction introduction/projection and universal introduction/elimination with
explicit side conditions. Search uses only modus ponens and conjunction
projection, with a maximum of 256 admitted steps. An unsuccessful search returns
`UNKNOWN`; it never establishes unprovability.

The catalogue separates Gödel's original variants, Rosser, the second theorem,
Löb, Tarski and the diagonal lemma. Each entry names its exact requirements,
sources, evidential status and limitations. For example:

```r
record <- lookup_statement("rosser")
record$requirements
check_applicability("rosser", theory_context("PA"))$status # UNKNOWN
```

A theory name does not establish its assumptions. `ESTABLISHED` from
`check_applicability()` means only conditional applicability under explicit user
declarations. A catalogue entry is literature evidence, not a formal proof;
a successful native derivation check trusts the supplied assumptions and axioms.
The package never establishes the consistency of PA or decides general truth.

`vignette("goedel")` describes the syntax, encoding, trust boundary and status
model. `help(package="goedel")` lists every public operation. The canonical
catalogue and reference cases are installed under `system.file("extdata",
package="goedel")`, so usage does not depend on a source checkout.

Version 0.2.0 adds explicit Q and PA presentations, induction-schema generation
and recognition, a safe formula parser, exact decimal numeral abbreviations,
finite structures with total interpretation tables, and natural deduction with
scopes, discharge, equality and eigenvariable checks. The original proof API
and bounded search remain available.

```r
pa <- arithmetic_theory("PA")
body <- parse_formula("x + y = y + x")
instance <- induction_axiom(body, "x")
is_axiom(pa, instance)            # TRUE: syntactic axiom membership
format_formula(instance)

model <- finite_structure(c("a", "b"))
evaluate_formula(parse_formula("forall x. x = x"), model)$status

p <- modal_atom("p")
frame <- kripke_model(c("a", "b"), list(list("a", "b")), list(p=list("b")))
evaluate_modal(modal_box(p), frame, "a")$status
frame_check(frame)
```

Finite evaluation concerns exactly the supplied structure or Kripke frame. An
exhaustive finite valuation check does not establish general modal completeness
or an arithmetical interpretation. Arbitrary unbounded truth, consistency and
proof search remain undecidable in general; no API simulates their solution.

Runtime dependencies are jsonlite, digest and gmp; R 4.1 or later is required.
Build and check a source package using `R CMD build .` and
`R CMD check --as-cran goedel_0.2.0.tar.gz`. The package does not access the network
or write into installed resources during normal use or tests.

The complete PA Hilbert proof checker and its concrete arithmetic representation
also support `proof_PA_formula()`, `provability_formula()` and the corresponding
`consistency_formula()`. `fixed_point()` and `godel_sentence()` construct actual
arithmetic DAGs and exact codes, with a native checked conditional equivalence
and an explicit trusted representation premise. Large constructions can require
millions of decimal digits. `check_metatheorem()` binds separate Goedel, Rosser,
Loeb and Tarski variants to their prerequisites and the exact reviewed predicate.
Independent mathematical review of the representation and D1/D2/D3 conditions
is recorded separately from formal kernel verification, which is not claimed.

The installed `system.file("reproduction", package="goedel")` directory contains
the public mathematical specifications, source programs and arithmetic compilers
needed to audit and reconstruct the representation resources. These reference
sources are separate from the native R runtime and are never executed implicitly.

Copyright 2026 RiskDataScience GmbH. Apache License 2.0.
Maintainer: Dr. Dimitrios Geromichalos <riskdatascience@web.de>.
