test_that("independently derived shared reference cases agree", {
  data <- jsonlite::fromJSON(system.file("extdata", "reference_cases.json", package = "goedel"), simplifyVector = FALSE)
  mapping <- list(applicability = function(id, declarations) check_applicability(id, theory_context("reference", declarations)), substitute = substitute_formula, serialize = serialize_record,
    search = bounded_proof_search, validate_error = validate_expr, decode_error = decode)
  for (case in data$cases) {
    fun <- mapping[[case$operation]]
    if (is.null(fun)) fun <- getExportedValue("goedel", case$operation)
    if (grepl("_error$", case$operation)) {
      code <- tryCatch({do.call(fun, case$arguments); "NO_ERROR"}, goedel_error = function(e) e$code)
      expect_identical(code, case$expected, info = case$id)
    } else {
      actual <- do.call(fun, case$arguments)
      if (inherits(actual, "goedel_expr")) {
        expect_identical(serialize_record(actual), serialize_record(case$expected), info = case$id)
      } else if (inherits(actual, "goedel_result")) {
        expect_identical(actual$status, case$expected, info = case$id)
      } else if (case$operation %in% c("free_variables", "bound_variables")) {
        expect_identical(actual, as.character(unlist(case$expected)), info = case$id)
      } else expect_equal(actual, case$expected, info = case$id)
    }
  }
})
