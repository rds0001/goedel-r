## Local candidate 0.2.0; not submitted

The local validation environment is Linux, R 4.1.2. Both `R CMD check --as-cran`
and `devtools::check` are part of candidate acceptance, including tests, examples,
the vignette and the PDF reference manual. Exact outcomes are recorded against
the candidate archive; historical version 0.1.0 results do not validate 0.2.0.

## Notes requiring explanation

* Installed size is approximately 5.4 MB, including 4.7 MB of mathematical
  `extdata`. These are explicit, inspectable arithmetic syntax graphs, numerical
  checker programs and their versioned provenance. They are necessary for the
  concrete fixed-point and provability constructions and for independent native
  R execution. The package does not download these resources at runtime.
* The local environment cannot contact the time service used by the future
  timestamp check. It also cannot resolve the CRAN repository hosts for online
  incoming checks. The candidate must be rechecked with working network/time
  services before submission; these checks are not claimed to have passed.

## Remaining platform checks

Current R release and R-devel, Windows/macOS, Win-builder/R-hub as applicable,
online incoming checks and reverse-dependency checks remain separate release
gates. They have not been executed in this local environment. No package has
been pushed, uploaded or submitted.
