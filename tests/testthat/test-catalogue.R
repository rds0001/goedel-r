test_that("catalogue exposes evidence and conditional applicability", {
  statements <- list_statements(); definitions <- list_definitions()
  expect_true(length(statements) >= 8L)
  expect_true(length(definitions) >= 10L)
  expect_identical(statements, sort(statements))
  expect_identical(lookup_statement(statements[[1L]])$id, statements[[1L]])
  expect_identical(definition(definitions[[1L]])$id, definitions[[1L]])
  expect_error(lookup_statement("missing"), class = "goedel_error")
  expect_error(definition("missing"), class = "goedel_error")
  expect_true(length(relation_graph()$edges) > 0L)
  expect_identical(nchar(catalogue_manifest()$sha256), 64L)
  expect_identical(catalogue_manifest()$catalogue_version, "0.2.0")
  for (id in statements) {
    row <- lookup_statement(id)
    keys <- unlist(row$requirements)
    yes <- setNames(rep(list(TRUE), length(keys)), keys)
    reviewed <- row$evidence$verification_status %in% c("INDEPENDENTLY_CHECKED", "FORMALLY_VERIFIED") && identical(row$evidence$review_status, "REVIEWED")
    expect_identical(check_applicability(id, theory_context("declared", yes))$status, if(reviewed) "ESTABLISHED" else "UNKNOWN")
    expect_identical(check_applicability(id, theory_context("empty"))$status, "UNKNOWN")
    no <- yes; no[[1L]] <- FALSE
    expected <- if (identical(no$consistent, FALSE) && (identical(no$omega_consistent, TRUE) || identical(no$sigma1_sound, TRUE))) "INCONSISTENT_CONTEXT" else if(reviewed) "NOT_APPLICABLE" else "UNKNOWN"
    expect_identical(check_applicability(id, theory_context("violated", no))$status, expected)
    expect_true(length(check_applicability(id, theory_context("empty"))$limitations) > 0L)
  }
  expect_identical(check_applicability("rosser", theory_context("bad", list(consistent = FALSE, omega_consistent = TRUE)))$status, "INCONSISTENT_CONTEXT")
  expect_identical(theory_context("PA")$consistency_status, "NOT_ESTABLISHED")
  expect_error(theory_context("T", list(consistent = NA)), class = "goedel_error")
  expect_error(theory_context("T", list(consistent = 1)), class = "goedel_error")
  expect_error(theory_context(""), class = "goedel_error")
  expect_identical(theory_context(strrep("\u00e4", 65))$id, strrep("\u00e4", 65))
  expect_error(theory_context(strrep("T", 129)), class = "goedel_error")
  expect_error(theory_context("T", setNames(list(TRUE), NA_character_)), class = "goedel_error")
  expect_identical(check_applicability("rosser", theory_context("T", list(consistent_extra = FALSE, omega_consistent = TRUE)))$status, "UNKNOWN")
})


test_that("unreviewed or nonliterature evidence cannot be promoted by declarations", {
  original <- lookup_statement("rosser")
  context <- theory_context("declared", setNames(rep(list(TRUE), length(original$requirements)), unlist(original$requirements)))
  for (review in c("DRAFT", "WITHDRAWN", "SUPERSEDED")) {
    row <- original; row$evidence$review_status <- review
    fn <- check_applicability
    environment(fn) <- new.env(parent = environment(check_applicability))
    environment(fn)$lookup_statement <- function(id) row
    expect_identical(fn("rosser", context)$status, "UNKNOWN")
  }
  for (variant in c("SOURCE_CHECKED", "DEFINITION")) {
    row <- original
    if (variant == "SOURCE_CHECKED") row$evidence$verification_status <- variant else row$evidence$kind <- variant
    fn <- check_applicability
    environment(fn) <- new.env(parent = environment(check_applicability))
    environment(fn)$lookup_statement <- function(id) row
    expect_identical(fn("rosser", context)$status, "UNKNOWN")
  }
  huge <- setNames(rep(list(TRUE), 1001L), paste0("a", seq_len(1001L)))
  code <- tryCatch(theory_context("T", huge), goedel_error = function(e) e$code)
  expect_identical(code, "RESOURCE_LIMIT")
})
