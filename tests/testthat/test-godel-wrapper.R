# Composition only: no full PA Goedel fixed point is computed here. The actual
# provability graph and wrapper negation run; only fixed_point is replaced.
# The returned sentinel is deliberately not a mathematical result or proof.

test_that("Goedel wrapper binds real negated provability and propagates results and limits", {
  predicate <- provability_formula()
  expect_identical(dag_fingerprint(predicate),
                  "58fcc5492a6ef053c6176075570f1486859c7cdb6cc765812d01f72bdb3ce2ad")
  syntax_hashes <- function(graph) {
    # Exact rooted syntax oracle: independent of sharing, sensitive to names.
    hashes <- character(length(graph$nodes))
    for (i in seq_along(graph$nodes)) {
      node <- graph$nodes[[i]]
      children <- hashes[as.integer(unlist(node$args, use.names=FALSE)) + 1L]
      hashes[[i]] <- digest::digest(paste(c(node$op,node$name,children),collapse="|"),
                                   algo="sha256",serialize=FALSE)
    }
    hashes
  }
  expected <- syntax_hashes(predicate)[[predicate$root+1L]]
  captured <- NULL
  calls <- 0L
  sentinel <- new.env(parent=emptyenv())
  sentinel$purpose <- "wrapper-only sentinel; not a construction result"
  # Clone the exported function's lexical environment without changing namespace
  # bindings. Its real provability_formula and negation helpers remain inherited.
  godel_sentence <- getExportedValue("goedel", "godel_sentence")
  bindings <- new.env(parent=environment(godel_sentence))
  environment(godel_sentence) <- bindings
  bindings$fixed_point <- function(phi) {
    calls <<- calls+1L
    captured <<- phi
    sentinel
  }
  expect_identical(godel_sentence(),sentinel)
  expect_identical(calls,1L)
  expect_identical(validate_arithmetic_dag(captured)$free_variables,list("x1"))
  node <- captured$nodes[[captured$root+1L]]
  expect_identical(node$op,"not")
  expect_identical(node$name,"")
  expect_length(node$args,1L)
  expect_identical(syntax_hashes(captured)[[node$args[[1L]]+1L]],expected)
  original_input <- captured
  calls <- 0L
  exhausted <- structure(list(message="test-only constructor resource limit",
                              call=NULL,code="RESOURCE_LIMIT"),
                         class=c("goedel_error","error","condition"))
  bindings$fixed_point <- function(phi) {
    calls <<- calls+1L
    captured <<- phi
    stop(exhausted)
  }
  caught <- tryCatch(godel_sentence(),goedel_error=function(e)e)
  expect_identical(caught,exhausted)
  expect_identical(caught$code,"RESOURCE_LIMIT")
  expect_identical(calls,1L)
  expect_identical(captured,original_input)
})
